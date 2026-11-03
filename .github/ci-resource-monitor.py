#!/usr/bin/env python3
"""Bounded, best-effort Linux resource observations for one Actions job.

No command lines or environment are recorded. Stop uses a private run-owned
sentinel, never a PID signal; the child also retains Actions process tracking.
"""
import argparse
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import time


INTERVAL = 15
MAX_SECONDS = 12 * 60 * 60
MAX_BYTES = 4 * 1024 * 1024
MIRROR_LOG = Path('/var/log/user-data.log')


class CloudMirror:
    """Optional EC2-only append to a fixed, already-collected bootstrap log."""
    def __init__(self, labels, run=subprocess.run):
        try:
            labels = json.loads(labels)
        except (ValueError, TypeError):
            labels = None
        self.enabled = isinstance(labels, list) and 'aglib-ec2-pilot' in labels
        self.run = run

    def append(self, line):
        if not self.enabled:
            return
        try:
            if not stat.S_ISREG(MIRROR_LOG.lstat().st_mode):
                self.enabled = False
                return
            result = self.run(['sudo', '-n', 'tee', '-a', str(MIRROR_LOG)],
                              input='LEAN_CI_RESOURCE ' + line, text=True,
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                              timeout=1, check=False)
            self.enabled = result.returncode == 0
        except (OSError, subprocess.TimeoutExpired):
            self.enabled = False


def numbers(path):
    try:
        return {parts[0].rstrip(':'): int(parts[1]) for line in path.read_text().splitlines()
                if len(parts := line.split()) >= 2 and parts[1].isdigit()}
    except (OSError, ValueError):
        return {}


def integer(path):
    try:
        return int(path.read_text().strip())
    except (OSError, ValueError):
        return None


def host_cpu(proc):
    try:
        values = [int(value) for value in (proc / 'stat').read_text().splitlines()[0].split()[1:9]]
        return sum(values), values[3] + values[4]
    except (OSError, ValueError, IndexError):
        return None


def control_groups(units):
    """One read-only systemd query per observation, including collected units."""
    if not units:
        return {}
    try:
        result = subprocess.run(['systemctl', 'show', '--property=Id', '--property=ControlGroup',
                                 '--', *units], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                text=True, timeout=2, check=False)
    except (OSError, subprocess.TimeoutExpired):
        return {}
    groups = {}
    for block in result.stdout.strip().split('\n\n'):
        fields = dict(line.split('=', 1) for line in block.splitlines() if '=' in line)
        if fields.get('Id') in units and fields.get('ControlGroup'):
            groups[fields['Id']] = fields['ControlGroup']
    return groups


class Sampler:
    def __init__(self, scope_dir, prefix, proc=Path('/proc'), cgroup=Path('/sys/fs/cgroup'),
                 resolve=control_groups, uid=None):
        self.scope_dir, self.prefix = scope_dir, prefix
        self.proc, self.cgroup, self.resolve = proc, cgroup.resolve(), resolve
        self.uid = os.getuid() if uid is None else uid
        self.previous_cpu = {}
        self.previous_host = None
        self.previous_time = None

    def observe(self, now):
        memory = numbers(self.proc / 'meminfo')
        row = {'host_mem_total_bytes': memory.get('MemTotal', 0) * 1024,
               'host_mem_available_bytes': memory.get('MemAvailable', 0) * 1024,
               'host_cpu_busy_percent': None, 'native_scopes_live': 0,
               'native_memory_readable_scopes': 0, 'native_peaks_readable_scopes': 0,
               'native_memory_stat_readable_scopes': 0, 'native_membership_readable_scopes': 0,
               'native_inactive_file_readable_scopes': 0, 'native_file_mapped_readable_scopes': 0,
               'native_cpu_delta_scopes': 0, 'native_memory_current_bytes': 0,
               'native_memory_peak_max_bytes': None, 'native_memory_anon_bytes': 0,
               'native_memory_file_bytes': 0, 'native_memory_inactive_file_bytes': None,
               'native_memory_file_mapped_bytes': None, 'native_cpu_cores': None, 'lean_frontends': 0}
        current_host = host_cpu(self.proc)
        if current_host and self.previous_host:
            total = current_host[0] - self.previous_host[0]
            idle = current_host[1] - self.previous_host[1]
            if total > 0 and 0 <= idle <= total:
                row['host_cpu_busy_percent'] = round(100 * (total - idle) / total, 3)
        self.previous_host = current_host
        units = []
        if not self.scope_dir.is_symlink():
            for marker in sorted(self.scope_dir.glob('*.scope'))[:128]:
                if not re.fullmatch(re.escape(self.prefix) + r'[0-9a-f]{20}[.]scope', marker.name):
                    continue
                try:
                    if not marker.is_symlink() and marker.read_text().strip() == marker.name:
                        units.append(marker.name)
                except OSError:
                    pass
        next_cpu, pids, cpu_delta = {}, set(), 0
        for unit, relative in self.resolve(units).items():
            if unit not in units or not relative.startswith('/'):
                continue
            group = (self.cgroup / relative.lstrip('/')).resolve()
            if not group.is_relative_to(self.cgroup) or group.name != unit or not group.is_dir():
                continue
            row['native_scopes_live'] += 1
            current = integer(group / 'memory.current')
            if current is not None:
                row['native_memory_readable_scopes'] += 1
                row['native_memory_current_bytes'] += current
            peak = integer(group / 'memory.peak')
            if peak is not None:
                row['native_peaks_readable_scopes'] += 1
                row['native_memory_peak_max_bytes'] = max(peak, row['native_memory_peak_max_bytes'] or 0)
            stats = numbers(group / 'memory.stat')
            if 'anon' in stats and 'file' in stats:
                row['native_memory_stat_readable_scopes'] += 1
                row['native_memory_anon_bytes'] += stats['anon']
                row['native_memory_file_bytes'] += stats['file']
            for name in ('inactive_file', 'file_mapped'):
                if name in stats:
                    row[f'native_{name}_readable_scopes'] += 1
                    field = f'native_memory_{name}_bytes'
                    row[field] = (row[field] or 0) + stats[name]
            usage = numbers(group / 'cpu.stat').get('usage_usec')
            if usage is not None:
                # The directory inode distinguishes a recreated cgroup with the same unit name.
                try:
                    identity = (unit, group.stat().st_ino)
                except OSError:
                    continue
                next_cpu[identity] = usage
                previous = self.previous_cpu.get(identity)
                if previous is not None and usage >= previous:
                    row['native_cpu_delta_scopes'] += 1
                    cpu_delta += usage - previous
            try:
                members = set()
                for membership in [group / 'cgroup.procs', *group.rglob('*/cgroup.procs')]:
                    members.update(int(pid) for pid in membership.read_text().split())
                pids.update(members)
                row['native_membership_readable_scopes'] += 1
            except (OSError, ValueError):
                pass
        for pid in pids:
            process = self.proc / str(pid)
            try:
                if process.stat().st_uid == self.uid and (process / 'exe').resolve(strict=True).name == 'lean':
                    row['lean_frontends'] += 1
            except OSError:
                pass  # Processes and --collect scopes may disappear between reads.
        if self.previous_time is not None and now > self.previous_time and row['native_cpu_delta_scopes']:
            row['native_cpu_cores'] = round(cpu_delta / 1_000_000 / (now - self.previous_time), 3)
        self.previous_cpu, self.previous_time = next_cpu, now
        return row


def owned_directory(path):
    metadata = path.lstat()
    if path.is_symlink() or not path.is_dir() or metadata.st_uid != os.getuid() or metadata.st_mode & 0o077:
        raise ValueError('Resource monitor directory must be private and owned by this runner')


def run_sampler(directory, sampler, seconds, interval=INTERVAL, mirror=None):
    owned_directory(directory)
    start = time.monotonic()
    output = directory / 'resources.jsonl'
    try:
        while time.monotonic() - start < min(seconds, MAX_SECONDS) and not (directory / 'stop').exists():
            now = time.monotonic()
            try:
                row = sampler.observe(now)
                row['elapsed_seconds'] = round(now - start, 3)
                row['unix_seconds'] = int(time.time())
                line = json.dumps(row, separators=(',', ':'), allow_nan=False) + '\n'
                if (output.stat().st_size if output.exists() else 0) + len(line) > MAX_BYTES:
                    break
                with output.open('a') as stream:
                    stream.write(line)
                if mirror:
                    mirror.append(line)
            except (OSError, ValueError):
                pass  # A transient /proc, cgroup or diagnostic failure must not affect CI.
            deadline = min(now + interval, start + min(seconds, MAX_SECONDS))
            while time.monotonic() < deadline and not (directory / 'stop').exists():
                time.sleep(min(0.25, max(0, deadline - time.monotonic())))
    finally:
        (directory / 'stopped').touch()


def stop(directory, summary=None):
    owned_directory(directory)
    # A sentinel cannot signal an unrelated/reused PID. Never call kill/pkill.
    (directory / 'stop').touch()
    deadline = time.monotonic() + 3
    while not (directory / 'stopped').exists() and time.monotonic() < deadline:
        time.sleep(0.1)
    if summary and (directory / 'resources.jsonl').is_file():
        rows = []
        for line in (directory / 'resources.jsonl').read_text()[:MAX_BYTES].splitlines():
            try:
                rows.append(json.loads(line))
            except ValueError:
                pass
        if rows:
            def maximum(name):
                return max((row.get(name) or 0 for row in rows), default=0)
            def memory_maximum(name, count):
                values = [row[name] for row in rows if row.get(count) and row.get(name) is not None]
                return f'{max(values) / 1048576:.0f} MiB' if values else 'unavailable'
            with summary.open('a') as stream:
                stream.write('\nResource observations (sampled coverage, not whole-run maxima): '
                             f'{len(rows)} samples; max simultaneous Lean processes '
                             f'{maximum("lean_frontends")}; max sampled native cgroup memory.current '
                             f'{memory_maximum("native_memory_current_bytes", "native_memory_readable_scopes")}; '
                             f'max observed individual cgroup memory.peak '
                             f'{memory_maximum("native_memory_peak_max_bytes", "native_peaks_readable_scopes")}. '
                             'Anon, file, inactive_file, file_mapped and host MemAvailable are separate JSONL fields; '
                             'file counters overlap and are not RSS or a measured working set.\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('start', 'sample', 'stop'))
    parser.add_argument('--minutes', type=float, default=360)
    args = parser.parse_args()
    identity = '-'.join(os.environ[name] for name in ('GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_JOB'))
    if not re.fullmatch(r'[0-9]+-[0-9]+-[A-Za-z0-9_-]+', identity):
        raise ValueError('Invalid Actions run identity')
    directory = Path(os.environ['RUNNER_TEMP']) / 'lean-ci-resources' / identity
    if args.action == 'start':
        if not 0 < args.minutes * 60 <= MAX_SECONDS:
            raise ValueError('Resource monitor duration must be positive and at most 12 hours')
        directory.parent.mkdir(exist_ok=True)
        directory.mkdir(mode=0o700)
        owned_directory(directory)
        # Inherit RUNNER_TRACKING_ID: Actions cleanup remains a second lifetime bound.
        subprocess.Popen([sys.executable, str(Path(__file__).resolve()), 'sample',
                          '--minutes', str(args.minutes)], stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    elif args.action == 'sample':
        scopes = Path(os.environ['RUNNER_TEMP']) / 'lean-ci-scopes' / identity
        run_sampler(directory, Sampler(scopes, 'lean-ci-' + identity + '-'), args.minutes * 60,
                    mirror=CloudMirror(os.environ.get('CI_RESOURCE_RUNNER_LABELS')))
    elif directory.exists():
        stop(directory, Path(os.environ['GITHUB_STEP_SUMMARY']) if os.environ.get('GITHUB_STEP_SUMMARY') else None)


if __name__ == '__main__':
    main()
