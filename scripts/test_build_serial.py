"""Serial source dependency order and capped-wrapper tests without Lean."""
from contextlib import nullcontext, redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import build_serial


class SerialBuildTests(unittest.TestCase):
    def test_build_threads_are_configurable_but_kernel_profile_stays_separate(self):
        with patch.object(build_serial.os, 'cpu_count', return_value=8):
            self.assertEqual(build_serial.build_threads({}), 1)
            self.assertEqual(build_serial.build_threads({'LEAN_NUM_THREADS': '2'}), 2)
            self.assertEqual(build_serial.build_threads(
                {'LEAN_NUM_THREADS': '1', 'AGLIB_BUILD_THREADS': '4'}), 4)
            for value in ['0', '-1', '9', 'invalid']:
                with self.assertRaises(ValueError):
                    build_serial.build_threads({'AGLIB_BUILD_THREADS': value})
        self.assertEqual(build_serial.limits(
            {'AGLIB_BUILD_THREADS': '4', 'LEAN_NUM_THREADS': '4'}, 64 * 1024**3)['lean_threads'], 1)

    def test_dependency_order_and_cycle_guard(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'A.lean').write_text('import B\nimport External.Missing\n')
            (root / 'B.lean').write_text('module\n')
            self.assertEqual(build_serial.source_order(root, ['A']), ['B', 'A'])
            (root / 'B.lean').write_text('import A\n')
            with self.assertRaisesRegex(ValueError, 'cycle'):
                build_serial.source_order(root, ['A'])

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

    def test_cached_shortcut_or_expected_cold_miss(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'A.lean').write_text('import B\n'); (root / 'B.lean').write_text('module\n')
            for index, (codes, expected) in enumerate([
                                    ([0], [['lake', '--no-build', 'build', 'A']]),
                                    ([3, 0], [['lake', '--no-build', 'build', 'A'],
                                              ['lake', 'build', 'A']])]):
                remaining = iter(codes)
                def fake_run(*args, **kwargs):
                    code = next(remaining)
                    if code == 3:
                        kwargs['stderr'].write('error: target is out-of-date and needs to be rebuilt\n')
                    return code
                with patch.object(build_serial, 'capped_toolchain', return_value=nullcontext({})), \
                        patch.object(build_serial, 'run', side_effect=fake_run) as run, \
                        redirect_stdout(io.StringIO()) as output:
                    directory = root / ('receipts-' + str(index))
                    self.assertEqual(build_serial.build(root, ['A'], directory), 0)
                    self.assertEqual([call.args[0] for call in run.call_args_list], expected)
                    self.assertTrue(all(call.kwargs['budget']['max_active_lean'] == 1
                                        for call in run.call_args_list))
                    self.assertTrue(all(call.kwargs['budget']['lean_threads'] == 1
                                        for call in run.call_args_list))
                    self.assertIn('Build cache ' + ('hit' if codes[0] == 0 else 'miss'), output.getvalue())
                    self.assertNotIn('error:', output.getvalue())
                    self.assertEqual(run.call_args_list[0].kwargs['stdout'].name,
                                     str(directory / 'cached-check.log'))

    def test_real_graph_compiler_failure_propagates_with_live_diagnostics(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); (root/'A.lean').write_text('module\n')
            def fake_run(command, **kwargs):
                if '--no-build' in command:
                    kwargs['stderr'].write('error: target is out-of-date and needs to be rebuilt\n')
                    return 3
                self.assertNotIn('stdout', kwargs)
                self.assertNotIn('stderr', kwargs)
                print('A.lean:1:0: error: real compiler failure', file=build_serial.sys.stderr)
                return 19
            with patch.object(build_serial, 'capped_toolchain', return_value=nullcontext({})), \
                    patch.object(build_serial, 'run', side_effect=fake_run) as run, \
                    redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(build_serial.build(root, ['A'], root/'receipts'), 19)
                self.assertEqual(run.call_count, 2)
                self.assertIn('real compiler failure', errors.getvalue())

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
