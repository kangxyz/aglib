"""Retained nonduplicated resource/build safety contracts for shared replay tooling."""
from contextlib import nullcontext, redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from lean_ci.execution import resources as guard, build as build_serial


class RetainedResourceContracts(unittest.TestCase):
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


    def test_wrapper_caps_actual_child_arguments_and_preserves_toolchain(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); prefix = root / 'toolchain'
            (prefix / 'bin').mkdir(parents=True); (prefix / 'lib').mkdir()
            lean = prefix / 'bin/lean'
            lean.write_text('#!/usr/bin/env python3\nimport json,os,sys\n'
                'print(json.dumps({"args":sys.argv[1:],"threads":os.environ["LEAN_NUM_THREADS"]}))\n')
            lean.chmod(0o755)
            before = lean.read_bytes()
            with patch.object(build_serial.subprocess, 'check_output', return_value=str(lean)):
                with build_serial.capped_toolchain(root, threads=3) as env:
                    wrapper = Path(env['LEAN'])
                    self.assertEqual((wrapper.parent.parent / 'lib').resolve(), (prefix / 'lib').resolve())
                    result = subprocess.run(['lean', '-j8', '-M999999', '-DautoImplicit=false',
                                             'File.lean'], env=env, capture_output=True, text=True,
                                            check=True)
                    actual = json.loads(result.stdout)
                    args = actual['args']
                    self.assertEqual(args[0], '-j3')
                    self.assertEqual(actual['threads'], '3')
                    self.assertEqual(env['LEAN_NUM_THREADS'], '1')
                    self.assertTrue(args[1].startswith('-M'))
                    self.assertEqual(args[2:], ['-DautoImplicit=false', 'File.lean'])
                    metadata = subprocess.run(['lean', '--githash'], env=env,
                                              capture_output=True, text=True, check=True)
                    actual = json.loads(metadata.stdout)
                    self.assertEqual(actual['args'][0], '-j1')
                    self.assertEqual(actual['threads'], '1')
                self.assertFalse(wrapper.exists())
            self.assertEqual(lean.read_bytes(), before)


    def test_native_output_mappings_forwarded_on_cached_and_cold_paths(self):
        for codes in ([0], [3, 0]):
            with self.subTest(codes=codes), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                (root / 'A.lean').write_text('module\n')
                remaining = iter(codes)
                def fake_run(command, **kwargs):
                    code = next(remaining)
                    if code == 3:
                        kwargs['stderr'].write('error: target is out-of-date and needs to be rebuilt\n')
                    self.assertEqual(command[-2:], ['-o', str((root / 'export/outputs.jsonl').resolve())])
                    self.assertIn('--rehash', command)
                    return code
                with patch.object(build_serial, 'capped_toolchain', return_value=nullcontext({})), \
                        patch.object(build_serial, 'run', side_effect=fake_run) as run, \
                        redirect_stdout(io.StringIO()):
                    self.assertEqual(build_serial.build(root, ['A'], root / 'receipts', True,
                                                        root / 'export/outputs.jsonl'), 0)
                    self.assertEqual(run.call_count, len(codes))
                    self.assertTrue((root / 'export').is_dir())


    def test_unexpected_probe_and_resource_errors_fail_without_compilation(self):
        for code, diagnostic in [(1, 'error: unknown target A\n'),
                (3, 'error: target is out-of-date and needs to be rebuilt\nerror: broken configuration\n'),
                (125, 'Resource guard unavailable\n'), (137, 'Resource guard: RSS cutoff\n')]:
            with self.subTest(code=code), tempfile.TemporaryDirectory() as temporary:
                root=Path(temporary); (root/'A.lean').write_text('module\n')
                def fake_run(*args, **kwargs):
                    kwargs['stderr'].write(diagnostic)
                    return code
                with patch.object(build_serial, 'capped_toolchain', return_value=nullcontext({})), \
                        patch.object(build_serial, 'run', side_effect=fake_run) as run, \
                        redirect_stderr(io.StringIO()) as errors:
                    self.assertEqual(build_serial.build(root, ['A'], root/'receipts'), code)
                    self.assertEqual(run.call_count, 1)
                    self.assertIn(diagnostic, errors.getvalue())


    def test_probe_log_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); (root/'A.lean').write_text('module\n')
            directory=root/'receipts'; directory.mkdir()
            log=directory/'cached-check.log'; log.write_text('earlier probe\n')
            with patch.object(build_serial, 'capped_toolchain', return_value=nullcontext({})), \
                    patch.object(build_serial, 'run') as run:
                with self.assertRaises(FileExistsError):
                    build_serial.build(root, ['A'], directory)
                run.assert_not_called()
            self.assertEqual(log.read_text(), 'earlier probe\n')


if __name__ == '__main__':
    unittest.main()
