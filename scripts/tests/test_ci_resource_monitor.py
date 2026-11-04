"""Resource observations and stop safety without systemd or Lean execution."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
from unittest.mock import Mock


ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / '.github/ci-resource-monitor.py'
spec = importlib.util.spec_from_file_location('ci_resource_monitor', HELPER)
monitor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(monitor)


class ResourceSampler(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='ci-resource-fixtures-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.proc, self.cgroups, self.scopes = (self.root / name for name in ('proc', 'cgroups', 'scopes'))
        for directory in (self.proc, self.cgroups, self.scopes):
            directory.mkdir()
        (self.proc / 'meminfo').write_text('MemTotal: 65536 kB\nMemAvailable: 40000 kB\nCached: 123 kB\n')
        (self.proc / 'stat').write_text('cpu  100 0 100 800 0 0 0 0 0 0\n')
        self.prefix = 'lean-ci-123-2-build-'
        self.groups = {}
        self.sampler = monitor.Sampler(self.scopes, self.prefix, self.proc, self.cgroups,
                                       resolve=lambda units: {unit: self.groups[unit] for unit in units
                                                              if unit in self.groups})

    def scope(self, suffix, current=100, peak=300, anon=60, file=40, cpu=1_000_000, pids=''):
        unit = self.prefix + suffix * 20 + '.scope'
        (self.scopes / unit).write_text(unit + '\n')
        group = self.cgroups / 'system.slice' / unit
        group.mkdir(parents=True)
        (group / 'memory.current').write_text(str(current))
        (group / 'memory.peak').write_text(str(peak))
        (group / 'memory.stat').write_text(f'anon {anon}\nfile {file}\nshmem 3\ninactive_file 10\nfile_mapped 5\n')
        (group / 'cpu.stat').write_text(f'usage_usec {cpu}\n')
        (group / 'cgroup.procs').write_text(pids)
        self.groups[unit] = '/system.slice/' + unit
        return group

    def process(self, pid, executable):
        binary = self.root / 'bin' / executable
        binary.parent.mkdir(exist_ok=True)
        binary.touch()
        process = self.proc / str(pid)
        process.mkdir()
        (process / 'exe').symlink_to(binary)

    def test_multiple_scopes_memory_cpu_deltas_and_frontend_membership(self):
        first = self.scope('a', pids='10\n11\n')
        second = self.scope('b', current=200, peak=500, anon=150, file=50, pids='10\n12\n999\n')
        child = second / 'child'
        child.mkdir()
        (child / 'cgroup.procs').write_text('13\n')
        for pid, executable in ((10, 'lean'), (11, 'lake'), (12, 'cc'), (13, 'lean'), (14, 'lean')):
            self.process(pid, executable)
        initial = self.sampler.observe(10)
        self.assertEqual(initial['host_mem_total_bytes'], 65536 * 1024)
        self.assertEqual(initial['host_mem_available_bytes'], 40000 * 1024)
        self.assertEqual(initial['native_scopes_live'], 2)
        self.assertEqual(initial['native_memory_current_bytes'], 300)
        self.assertEqual(initial['native_memory_peak_max_bytes'], 500)  # Individual peaks are not summed.
        self.assertEqual(initial['native_memory_anon_bytes'], 210)
        self.assertEqual(initial['native_memory_file_bytes'], 90)
        self.assertEqual(initial['native_memory_inactive_file_bytes'], 20)
        self.assertEqual(initial['native_memory_file_mapped_bytes'], 10)
        self.assertEqual(initial['native_inactive_file_readable_scopes'], 2)
        self.assertEqual(initial['lean_frontends'], 2)  # Neither threads nor out-of-scope Lean.
        self.assertIsNone(initial['native_cpu_cores'])
        (first / 'cpu.stat').write_text('usage_usec 16000000\n')
        (second / 'cpu.stat').write_text('usage_usec 31000000\n')
        (self.proc / 'stat').write_text('cpu  200 0 200 1000 0 0 0 0 0 0\n')
        observed = self.sampler.observe(25)
        self.assertEqual(observed['native_cpu_cores'], 3)
        self.assertEqual(observed['native_cpu_delta_scopes'], 2)
        self.assertEqual(observed['host_cpu_busy_percent'], 50)
        self.assertTrue(all(value is None or isinstance(value, (float, int)) for value in observed.values()))

    def test_collected_scopes_missing_metrics_and_counter_resets_are_partial_coverage(self):
        group = self.scope('a')
        self.sampler.observe(0)
        (group / 'memory.peak').unlink()
        (group / 'memory.stat').unlink()
        (group / 'cpu.stat').write_text('usage_usec 1\n')
        row = self.sampler.observe(15)
        self.assertIsNone(row['native_memory_peak_max_bytes'])
        self.assertEqual(row['native_peaks_readable_scopes'], 0)
        self.assertEqual(row['native_memory_stat_readable_scopes'], 0)
        self.assertIsNone(row['native_cpu_cores'])
        self.groups.clear()  # A --collect unit disappeared before the systemd query.
        row = self.sampler.observe(30)
        self.assertEqual(row['native_scopes_live'], 0)
        self.assertEqual(row['native_memory_readable_scopes'], 0)

    def test_foreign_markers_symlinks_paths_and_process_owners_are_excluded(self):
        group = self.scope('a', pids='10\n')
        self.process(10, 'lean')
        self.sampler.uid = os.getuid() + 1
        self.assertEqual(self.sampler.observe(0)['lean_frontends'], 0)
        marker = self.scopes / group.name
        marker.write_text('different scope\n')
        self.assertEqual(self.sampler.observe(15)['native_scopes_live'], 0)
        marker.unlink()
        target = self.root / 'external-marker'
        target.write_text(group.name)
        marker.symlink_to(target)
        self.assertEqual(self.sampler.observe(30)['native_scopes_live'], 0)
        marker.unlink()
        marker.write_text(group.name)
        self.groups[group.name] = '/../../outside/' + group.name
        self.assertEqual(self.sampler.observe(45)['native_scopes_live'], 0)

    def test_systemd_query_handles_multiple_and_disappearing_units(self):
        result = subprocess.CompletedProcess([], 1, 'Id=one.scope\nControlGroup=/system.slice/one.scope\n\n'
                                                    'Id=gone.scope\nControlGroup=\n')
        with patch.object(monitor.subprocess, 'run', return_value=result) as command:
            self.assertEqual(monitor.control_groups(['one.scope', 'gone.scope']),
                             {'one.scope': '/system.slice/one.scope'})
            self.assertEqual(command.call_args.kwargs['timeout'], 2)
            self.assertNotIn('sudo', command.call_args.args[0])
        with patch.object(monitor.subprocess, 'run', side_effect=subprocess.TimeoutExpired('systemctl', 2)):
            self.assertEqual(monitor.control_groups(['one.scope']), {})

    def test_output_and_lifetime_are_bounded_and_stop_uses_no_pid_signal(self):
        directory = self.root / 'monitor'
        directory.mkdir(mode=0o700)
        started = time.monotonic()
        monitor.run_sampler(directory, self.sampler, seconds=0.06, interval=10)
        self.assertLess(time.monotonic() - started, 0.5)
        self.assertTrue((directory / 'stopped').exists())
        rows = [json.loads(line) for line in (directory / 'resources.jsonl').read_text().splitlines()]
        self.assertEqual(len(rows), 1)
        self.assertNotIn('PATH', str(rows))
        summary = self.root / 'summary'
        with patch.object(monitor.os, 'kill', side_effect=AssertionError('PID signaling is forbidden')):
            monitor.stop(directory, summary)
        self.assertTrue((directory / 'stop').exists())
        self.assertIn('## Resource observations\n\n| Metric | Observed value |', summary.read_text())
        self.assertIn('sampled intervals', summary.read_text())
        output = directory / 'resources.jsonl'
        previous_size = output.stat().st_size
        (directory / 'stop').unlink()
        with patch.object(monitor, 'MAX_BYTES', previous_size):
            monitor.run_sampler(directory, self.sampler, seconds=0.06, interval=0.01)
        self.assertEqual(output.stat().st_size, previous_size)

    def test_stop_sentinel_ends_a_live_sampler_and_rejects_foreign_directories(self):
        directory = self.root / 'monitor'
        directory.mkdir(mode=0o700)
        thread = threading.Thread(target=monitor.run_sampler,
                                  args=(directory, self.sampler, 2), kwargs={'interval': 15})
        thread.start()
        try:
            monitor.stop(directory)
        finally:
            thread.join(timeout=3)
        self.assertFalse(thread.is_alive())
        link = self.root / 'monitor-link'
        link.symlink_to(directory, target_is_directory=True)
        with self.assertRaises(ValueError):
            monitor.stop(link)
        directory.chmod(0o755)
        with self.assertRaises(ValueError):
            monitor.stop(directory)

    def test_cli_start_and_stop_keep_logs_scalar_without_environment(self):
        environment = {**os.environ, 'RUNNER_TEMP': str(self.root), 'GITHUB_RUN_ID': '123',
                       'GITHUB_RUN_ATTEMPT': '2', 'GITHUB_JOB': 'test_lint',
                       'NOT_LOGGED': 'private-resource-fixture', 'RUNNER_TRACKING_ID': 'fixture-tracking'}
        result = subprocess.run([sys.executable, str(HELPER), 'start', '--minutes', '0.02'],
                                env=environment, capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        directory = self.root / 'lean-ci-resources/123-2-test_lint'
        try:
            deadline = time.monotonic() + 2
            while not (directory / 'resources.jsonl').exists() and time.monotonic() < deadline:
                time.sleep(0.02)
            result = subprocess.run([sys.executable, str(HELPER), 'stop'], env=environment,
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((directory / 'stopped').exists())
            text = (directory / 'resources.jsonl').read_text()
            self.assertNotIn('private-resource-fixture', text)
            self.assertNotIn('fixture-tracking', text)
            self.assertTrue(all(value is None or isinstance(value, (float, int))
                                for line in text.splitlines() for value in json.loads(line).values()))
        finally:
            (directory / 'stop').touch()

    def test_live_mirror_is_exact_label_fixed_existing_regular_file_and_fail_soft(self):
        path = self.root / 'bootstrap.log'
        path.touch()
        run = Mock(return_value=subprocess.CompletedProcess([], 0))
        line = '{"native_memory_current_bytes":123}\n'
        with patch.object(monitor, 'MIRROR_LOG', path):
            for labels in ('["ubuntu-24.04"]', '["aglib-ec2-pilot-other"]', '"aglib-ec2-pilot"', 'invalid'):
                monitor.CloudMirror(labels, run=run).append(line)
            run.assert_not_called()
            mirror = monitor.CloudMirror('["self-hosted","linux","x64","aglib-ec2-pilot"]', run=run)
            mirror.append(line)
            self.assertEqual(run.call_args.args[0], ['sudo', '-n', 'tee', '-a', str(path)])
            self.assertEqual(run.call_args.kwargs['input'], 'LEAN_CI_RESOURCE ' + line)
            self.assertEqual(run.call_args.kwargs['timeout'], 1)
            self.assertEqual(run.call_args.kwargs['stdout'], subprocess.DEVNULL)
            self.assertEqual(run.call_args.kwargs['stderr'], subprocess.DEVNULL)
            run.reset_mock()
            path.unlink()
            path.symlink_to(self.proc / 'meminfo')
            mirror.append(line)
            run.assert_not_called()
            self.assertFalse(mirror.enabled)
            path.unlink()
            path.touch()
            for failure in (subprocess.TimeoutExpired('sudo', 1), OSError('not available')):
                failed = Mock(side_effect=failure)
                mirror = monitor.CloudMirror('["aglib-ec2-pilot"]', run=failed)
                mirror.append(line)
                mirror.append(line)
                self.assertEqual(failed.call_count, 1)
                self.assertFalse(mirror.enabled)
            failed = Mock(return_value=subprocess.CompletedProcess([], 1))
            mirror = monitor.CloudMirror('["aglib-ec2-pilot"]', run=failed)
            mirror.append(line)
            self.assertFalse(mirror.enabled)


if __name__ == '__main__':
    unittest.main()
