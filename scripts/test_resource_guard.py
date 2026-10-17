"""Small-process and injected-sample tests; never launch Lean."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from contextlib import nullcontext, redirect_stderr
import io

import resource_guard as guard


class ResourceGuardTests(unittest.TestCase):
    def test_direct_capped_frontends_preserve_arguments(self):
        environment = {'LEAN': '/owned overlay/bin/lean'}
        tail = ['--setup', 'setup with spaces.json', '-DautoImplicit=false', 'File.lean']
        cases = [(['lean', *tail], [environment['LEAN'], *tail]),
                 (['lake', 'env', 'lean', *tail], ['lake', 'env', environment['LEAN'], *tail]),
                 (['/pinned/bin/lake', 'env', 'lean', *tail],
                  ['/pinned/bin/lake', 'env', environment['LEAN'], *tail]),
                 (['/usr/bin/time', '-lp', 'lake', 'env', 'lean', *tail],
                  ['/usr/bin/time', '-lp', 'lake', 'env', environment['LEAN'], *tail]),
                 (['/usr/bin/time', '-lp', 'lean', *tail],
                  ['/usr/bin/time', '-lp', environment['LEAN'], *tail])]
        for command, expected in cases:
            with self.subTest(command=command):
                before = list(command)
                self.assertEqual(guard.capped_command(command, environment), expected)
                self.assertEqual(command, before)

    def test_unsupported_direct_launch_forms_fail_closed(self):
        commands = [['lake', 'env'], ['lake', 'env', '/native/bin/lean', 'File.lean'],
                    ['lake', '--offline', 'env', 'lean', 'File.lean'],
                    ['lake', 'env', 'python3', '-c', 'pass'],
                    ['/native/bin/lean', 'File.lean'],
                    ['/usr/bin/time', '-p', 'lake', 'env', 'lean'],
                    ['/usr/bin/time', '-lp', 'python3', '-c', 'pass'],
                    ['sh', '-c', 'lake env lean File.lean']]
        for command in commands:
            with self.subTest(command=command), self.assertRaises(ValueError):
                guard.capped_command(command, {'LEAN': '/owned/lean'})

    def test_non_frontend_commands_are_not_rewritten_as_nested_shell_syntax(self):
        for command in [['lake', '--rehash', '--no-build', 'query', '+Aglib.Basic:setup'],
                        ['python3', 'driver.py', 'lake', 'env', 'lean']]:
            self.assertEqual(guard.capped_command(command, {'LEAN': '/owned/lean'}), command)

    def test_capped_cli_selects_child_threads_and_preserves_parent_and_memory_limits(self):
        chosen = guard.limits({'AGLIB_LEAN_MEMORY_MB': '4096', 'AGLIB_RSS_LIMIT_MB': '5120'},
                              7 * 1024**3)
        environment = {'LEAN': '/owned/lean', 'LEAN_NUM_THREADS': '1'}
        argv = ['guard', '--receipt', '/unused/receipt.json', '--capped-toolchain', '--',
                'lake', 'env', 'lean', '--setup', 'setup.json', 'File.lean']
        with patch.object(sys, 'argv', argv), \
                patch.dict(guard.os.environ, {'AGLIB_BUILD_THREADS': '4', 'LEAN_NUM_THREADS': '1'}, clear=True), \
                patch('build_serial.os.cpu_count', return_value=8), \
                patch.object(guard, 'limits', return_value=chosen), \
                patch('build_serial.capped_toolchain', return_value=nullcontext(environment)) as capped, \
                patch.object(guard, 'run', return_value=7) as run:
            self.assertEqual(guard.main(), 7)
        capped.assert_called_once_with(Path.cwd(), threads=4)
        self.assertEqual(run.call_args.args[0],
                         ['lake', 'env', '/owned/lean', '--setup', 'setup.json', 'File.lean'])
        self.assertEqual(run.call_args.kwargs['env']['LEAN_NUM_THREADS'], '1')
        budget = run.call_args.kwargs['budget']
        self.assertEqual((budget['lean_threads'], budget['native_build_threads'], budget['max_active_lean']),
                         (1, 4, 1))
        self.assertEqual((budget['lean_memory_mb'], budget['rss_limit_mb']), (4096, 5120))

    def test_invalid_selected_threads_prevent_capped_launch(self):
        with patch.object(sys, 'argv', ['guard', '--receipt', '/unused/receipt.json',
                                       '--capped-toolchain', '--', 'lean', 'File.lean']), \
                patch.dict(guard.os.environ, {'AGLIB_BUILD_THREADS': '0'}), \
                patch('build_serial.capped_toolchain') as capped, \
                patch.object(guard, 'run') as run, redirect_stderr(io.StringIO()):
            self.assertEqual(guard.main(), 125)
        capped.assert_not_called()
        run.assert_not_called()

    def test_cache_bootstrap_cannot_relax_other_commands(self):
        base = ['guard', '--receipt', '/unused/receipt.json', '--bootstrap-cache', '--']
        with patch.object(sys, 'argv', base + ['lake', 'build', 'Aglib']), \
                patch.object(guard, 'run') as run, redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                guard.main()
            self.assertEqual(error.exception.code, 2)
            run.assert_not_called()
        with patch.object(sys, 'argv', base + ['lake', 'exe', 'cache', 'get']), \
                patch('build_serial.capped_toolchain', return_value=nullcontext({})), \
                patch.object(guard, 'run', return_value=0) as run:
            self.assertEqual(guard.main(), 0)
            self.assertIsNone(run.call_args.kwargs['budget']['max_active_lean'])
            self.assertLess(run.call_args.kwargs['budget']['rss_limit_mb'], 28610)

    def test_default_and_ci_budgets_have_physical_and_user_margin(self):
        self.assertEqual(guard.limits({}, 64 * 1024**3)['rss_limit_mb'], 25600)
        ci = guard.limits({'AGLIB_LEAN_MEMORY_MB': '4096', 'AGLIB_RSS_LIMIT_MB': '5120'},
                          7 * 1024**3)
        self.assertLess(ci['lean_memory_mb'], ci['rss_limit_mb'])
        for env in [{'AGLIB_RSS_LIMIT_MB': '65000'}, {'AGLIB_LEAN_MEMORY_MB': '25600'},
                    {'AGLIB_LEAN_MEMORY_MB': '0'}, {'AGLIB_RSS_LIMIT_MB': 'invalid'}]:
            with self.assertRaises(ValueError):
                guard.limits(env, 64 * 1024**3)

    def test_large_host_explicit_override_and_existing_default_invariance(self):
        chosen = guard.limits({'AGLIB_LEAN_MEMORY_MB': '49152', 'AGLIB_RSS_LIMIT_MB': '65536'},
                              128 * 1024**3)
        self.assertEqual((chosen['lean_memory_mb'], chosen['rss_limit_mb']), (49152, 65536))
        default = guard.limits({}, 64 * 1024**3)
        self.assertEqual((default['lean_memory_mb'], default['rss_limit_mb']), (24576, 25600))

    def test_fourteen_gb_explicit_caps_keep_os_reserve(self):
        explicit = {'AGLIB_LEAN_MEMORY_MB': '10240', 'AGLIB_RSS_LIMIT_MB': '11264'}
        for physical in [14 * 1024**3, 14_000_000_000]:
            chosen = guard.limits(explicit, physical)
            self.assertGreaterEqual(physical - chosen['rss_limit_mb'] * guard.MIB, 2 * 1024**3)
            default = guard.limits({}, physical)
            self.assertLessEqual(default['rss_limit_mb'] * guard.MIB, physical * 3 // 4)
        with self.assertRaises(ValueError):
            guard.limits({'AGLIB_LEAN_MEMORY_MB': '10240', 'AGLIB_RSS_LIMIT_MB': '12289'},
                         14 * 1024**3)

    def test_only_exact_locator_actions_are_metadata(self):
        budget = guard.limits({}, 64 * 1024**3)
        cap = '-M' + str(budget['lean_memory_mb'])
        for argv in [['--githash'], ['--print-prefix'], ['-j1', cap, '--githash']]:
            self.assertTrue(guard.metadata_argv(argv, budget))
        for argv in [[], ['--githash', '--print-prefix'], ['--githash', 'File.lean'],
                     ['--print-prefix', '--run'], ['--githash', '--setup', 'x'],
                     ['--githash', '-j2'], ['--githash', '-M0'], ['--version']]:
            self.assertFalse(guard.metadata_argv(argv, budget))
        budget['lean_threads'] = 4
        self.assertTrue(guard.metadata_argv(['-j4', cap, '--githash'], budget))
        self.assertFalse(guard.metadata_argv(['-j1', cap, '--githash'], budget))

    def test_child_receives_its_recorded_thread_profile(self):
        budget = guard.limits({}, 64 * 1024**3)
        budget['lean_threads'] = 3
        code = guard.run([sys.executable, '-c',
                          'import os;assert os.environ["LEAN_NUM_THREADS"]=="3"'],
                         budget=budget, sampler=lambda _: [])
        self.assertEqual(code, 0)

    def test_metadata_query_handles_linux_and_darwin_process_names(self):
        budget = guard.limits({}, 64 * 1024**3)
        command = '/toolchain/bin/lean -j1 -M' + str(budget['lean_memory_mb']) + ' --githash\n'
        for path in ['lean', '/toolchain/bin/lean']:
            with patch.object(guard.subprocess, 'run', return_value=
                              subprocess.CompletedProcess([], 0, command, '')):
                self.assertTrue(guard.metadata_process(
                    {'pid': 123, 'executable': 'lean', 'command_path': path}, budget))
        with patch.object(guard.subprocess, 'run', return_value=
                          subprocess.CompletedProcess([], 0, command.strip() + ' File.lean', '')):
            self.assertFalse(guard.metadata_process({'pid': 123, 'executable': 'lean'}, budget))
        with patch.object(guard.subprocess, 'run') as process:
            self.assertFalse(guard.metadata_process({'pid': 123, 'executable': 'leanchecker'}, budget))
            process.assert_not_called()

    def test_monitor_failure_prevents_launch(self):
        with patch.object(guard, 'subprocess') as process:
            with self.assertRaises(RuntimeError):
                guard.run([sys.executable, '-c', 'raise SystemExit(0)'],
                          sampler=lambda _: (_ for _ in ()).throw(RuntimeError('ps denied')))
            process.Popen.assert_not_called()

    def test_exit_code_and_closure_are_recorded(self):
        with tempfile.TemporaryDirectory() as directory:
            receipt = Path(directory) / 'receipt.json'
            code = guard.run([sys.executable, '-c', 'raise SystemExit(7)'],
                             receipt=receipt, sampler=lambda _: [])
            data = json.loads(receipt.read_text())
            self.assertEqual(code, 7)
            self.assertTrue(data['owned_group_gone'])
            self.assertIsNone(data['guard_failure'])

    def test_rss_and_concurrency_failures_kill_only_owned_group(self):
        budget = guard.limits({}, 64 * 1024**3)
        for sample in [[{'rss_bytes': budget['rss_limit_mb'] * guard.MIB,
                         'executable': 'python'}],
                       [{'rss_bytes': 1, 'executable': 'lean'}] * 2]:
            with self.subTest(sample=sample), tempfile.TemporaryDirectory() as directory:
                class Child:
                    pid = 123456789
                    def wait(self): return -15
                child = Child()
                calls = 0
                def sampler(group):
                    nonlocal calls
                    calls += 1
                    return sample if calls == 2 else []
                with patch.object(guard.subprocess, 'Popen', return_value=child), \
                        patch.object(guard, 'terminate_group') as kill, \
                        patch.object(guard, 'metadata_process', return_value=False), \
                        patch.object(guard.time, 'sleep'), redirect_stderr(io.StringIO()):
                    code = guard.run(['recorded-command'], sampler=sampler, budget=budget,
                                     receipt=Path(directory) / 'receipt.json')
                self.assertNotEqual(code, 0)
                self.assertTrue(all(call.args[0] == child.pid for call in kill.call_args_list))
                self.assertNotEqual(child.pid, __import__('os').getpgrp())

    def test_signal_targets_are_rechecked_positive_owned_pids(self):
        with patch.object(guard, 'group_processes', side_effect=[
                [{'pid': 111}, {'pid': 222}], []]), \
                patch.object(guard.os, 'getpgid', side_effect=[888, 999]), \
                patch.object(guard.os, 'kill') as kill, \
                patch.object(guard.time, 'sleep'):
            guard.terminate_group(999)
        self.assertEqual([call.args[0] for call in kill.call_args_list], [111])

    def test_monitor_loss_still_signals_known_owned_leader(self):
        with patch.object(guard, 'group_processes', side_effect=RuntimeError('monitor lost')), \
                patch.object(guard.os, 'getpgid', return_value=999), \
                patch.object(guard.os, 'kill') as kill, \
                patch.object(guard.time, 'sleep'):
            guard.terminate_group(999, [{'pid': 111}])
        self.assertEqual({call.args[0] for call in kill.call_args_list}, {111, 999})


if __name__ == '__main__':
    unittest.main()
