#!/usr/bin/env python3
"""Run one owned process group with sampled RSS and Lean concurrency limits."""
import argparse
import json
import os
from pathlib import Path
import signal
import shlex
import subprocess
import sys
import time

MIB = 1024 * 1024


def limits(environment=None, physical_bytes=None):
    environment = os.environ if environment is None else environment
    if physical_bytes is None:
        physical_bytes = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
    physical_mb = physical_bytes // MIB
    ceiling = physical_mb - 2048
    default_rss = min(25600, ceiling, physical_mb * 3 // 4)
    default_native = min(24576, physical_mb // 2, default_rss - 64)
    native = int(environment.get('AGLIB_LEAN_MEMORY_MB', default_native))
    rss = int(environment.get('AGLIB_RSS_LIMIT_MB', default_rss))
    if not 64 <= native < rss <= ceiling:
        raise ValueError('Require 64 <= Lean MiB < group RSS MiB <= physical RAM minus 2048 MiB')
    return {'lean_memory_mb': native, 'rss_limit_mb': rss, 'sample_seconds': 0.1,
            'physical_memory_bytes': physical_bytes, 'lean_threads': 1, 'max_active_lean': 1}


def frontend_args(lean='lean'):
    return [lean, '-j1', '-M' + str(limits()['lean_memory_mb'])]


def capped_command(command, environment):
    """Bind supported direct frontends; Lake's augmented PATH can bypass our wrapper."""
    command = list(command)
    executable = Path(command[0]).name
    if executable == 'time':
        if command[:2] != ['/usr/bin/time', '-lp'] or len(command) < 3:
            raise ValueError('Capped timing supports only /usr/bin/time -lp COMMAND')
        if Path(command[2]).name not in {'lake', 'lean'}:
            raise ValueError('Capped timing requires a direct Lean or Lake command')
        return command[:2] + capped_command(command[2:], environment)
    if executable in {'sh', 'bash', 'zsh', 'dash', 'fish', 'env'}:
        raise ValueError('Capped frontends require a direct command, not a shell or env wrapper')
    if executable == 'lean':
        if command[0] != 'lean':
            raise ValueError('Use bare lean to select the capped pinned compiler')
        return [environment['LEAN'], *command[1:]]
    if executable == 'lake' and 'env' in command[1:]:
        if command[1:3] != ['env', 'lean']:
            raise ValueError('Capped Lake env supports only lake env lean ARGUMENTS')
        return command[:2] + [environment['LEAN']] + command[3:]
    return command


def group_processes(group):
    result = subprocess.run(['ps', '-eo', 'pid=,pgid=,rss=,comm='],
                            capture_output=True, text=True, check=True)
    selected = []
    for line in result.stdout.splitlines():
        parts = line.strip().split(None, 3)
        if len(parts) != 4:
            raise RuntimeError('Malformed ps RSS sample')
        pid, pgid, rss, executable = parts
        if int(pgid) == group:
            selected.append({'pid': int(pid), 'rss_bytes': int(rss) * 1024,
                             'executable': Path(executable).name, 'command_path': executable})
    return selected


def metadata_argv(arguments, budget):
    """Only one exact read-only locator action, with our injected resource flags."""
    actions = [arg for arg in arguments if arg in {'--githash', '--print-prefix'}]
    permitted = {'-j' + str(budget['lean_threads']), '-M' + str(budget['lean_memory_mb'])}
    return len(actions) == 1 and all(arg == actions[0] or arg in permitted for arg in arguments)


def metadata_process(member, budget):
    if member['executable'] != 'lean':
        return False
    result = subprocess.run(['ps', '-p', str(member['pid']), '-o', 'args='],
                            capture_output=True, text=True)
    if result.returncode or not result.stdout.strip():
        try:
            os.getpgid(member['pid'])
        except ProcessLookupError:
            return True  # the snapshot's process has already exited
        return False
    arguments = shlex.split(result.stdout.strip())
    # Darwin's comm is usually an absolute path; Linux's comm is a basename.
    return bool(arguments) and Path(arguments[0]).name == member['executable'] \
        and metadata_argv(arguments[1:], budget)


def terminate_group(group, known=()):
    for sig in [signal.SIGTERM, signal.SIGKILL]:
        try:
            members = group_processes(group)
        except (OSError, RuntimeError, subprocess.SubprocessError):
            members = list(known) + [{'pid': group}]
        if not members:
            return
        # Some macOS sandboxes reject negative-pgid kill operations. Signal only
        # enumerated positive PIDs after rechecking their actual owned group.
        for member in reversed(members):
            try:
                if os.getpgid(member['pid']) == group:
                    os.kill(member['pid'], sig)
            except ProcessLookupError:
                pass
        time.sleep(0.2)


def run(command, *, cwd=None, env=None, receipt=None, sampler=group_processes, budget=None,
        stdout=None, stderr=None):
    budget = limits() if budget is None else budget
    environment = dict(os.environ if env is None else env,
                       LEAN_NUM_THREADS=str(budget['lean_threads']))
    started = time.monotonic()
    # Probe monitoring permission before starting any potentially expensive work.
    sampler(os.getpgrp())
    child = subprocess.Popen(command, cwd=cwd, env=environment, start_new_session=True,
                             stdout=stdout, stderr=stderr)
    group = child.pid
    peak, reason, members = 0, None, []
    try:
        if receipt is not None:
            path = Path(receipt)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({'state': 'running', 'pid': child.pid, 'pgid': group,
                                        'command': list(command), 'limits': budget}, indent=2) + '\n')
        while True:
            members = sampler(group)
            rss = sum(member['rss_bytes'] for member in members)
            peak = max(peak, rss)
            lean_members = [member for member in members
                            if member['executable'] in {'lean', 'leanchecker'}]
            lean_count = len(lean_members)
            if budget['max_active_lean'] is not None and lean_count > budget['max_active_lean']:
                lean_count = sum(not metadata_process(member, budget) for member in lean_members)
            if rss >= budget['rss_limit_mb'] * MIB:
                reason = 'owned process group exceeded RSS cutoff'
            elif budget['max_active_lean'] is not None and lean_count > budget['max_active_lean']:
                reason = 'more than one active Lean process'
            if reason:
                terminate_group(group, members)
                break
            if child.poll() is not None:
                if sampler(group):
                    reason = 'child exited with live owned descendants'
                    terminate_group(group, members)
                break
            time.sleep(budget['sample_seconds'])
    except BaseException as error:
        reason = 'watchdog failed closed: ' + repr(error)
        terminate_group(group, members)
    code = child.wait()
    try:
        remaining = sampler(group)
    except BaseException as error:
        remaining = ['cannot verify closure: ' + repr(error)]
    if remaining:
        reason = reason or 'owned group closure could not be verified'
    result = {'state': 'completed', 'command': list(command), 'cwd': str(cwd or Path.cwd()), 'pid': child.pid,
              'pgid': group, 'exit_code': code, 'guard_failure': reason, 'peak_rss_bytes': peak,
              'duration_seconds': time.monotonic() - started, 'limits': budget,
              'owned_group_gone': not remaining, 'last_members': members}
    if receipt is not None:
        path = Path(receipt)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(result, indent=2) + '\n')
    if reason:
        print('Resource guard: ' + reason, file=sys.stderr)
        return 137 if 'RSS' in reason else 125
    return code if code >= 0 else 128 - code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--bootstrap-cache', action='store_true',
                        help='allow cache-tool compiler fanout only for exact lake exe cache get; RSS cap stays')
    parser.add_argument('--capped-toolchain', action='store_true',
                        help='supply selected native -j/-M caps for supported direct frontends')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('a command after -- is required')
    budget = limits()
    if args.bootstrap_cache:
        if command != ['lake', 'exe', 'cache', 'get']:
            parser.error('--bootstrap-cache permits only exact lake exe cache get')
        budget['max_active_lean'] = None
    try:
        if args.bootstrap_cache or args.capped_toolchain:
            from build_serial import build_threads, capped_toolchain
            threads = 1 if args.bootstrap_cache else build_threads()
            budget['native_build_threads'] = threads
            with capped_toolchain(Path.cwd(), threads=threads) as env:
                bounded = command if args.bootstrap_cache else capped_command(command, env)
                return run(bounded, receipt=args.receipt, budget=budget, env=env)
        return run(command, receipt=args.receipt, budget=budget)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print('Resource guard unavailable: ' + str(error), file=sys.stderr)
        return 125


if __name__ == '__main__':
    raise SystemExit(main())
