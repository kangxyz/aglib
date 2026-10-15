"""Serial source dependency order and capped-wrapper tests without Lean."""
from contextlib import nullcontext
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
            lean.write_text('#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(sys.argv[1:]))\n')
            lean.chmod(0o755)
            before = lean.read_bytes()
            with patch.object(build_serial.subprocess, 'check_output', return_value=str(lean)):
                with build_serial.capped_toolchain(root, threads=3) as env:
                    wrapper = Path(env['LEAN'])
                    self.assertEqual((wrapper.parent.parent / 'lib').resolve(), (prefix / 'lib').resolve())
                    result = subprocess.run(['lean', '-j8', '-M999999', '-DautoImplicit=false',
                                             'File.lean'], env=env, capture_output=True, text=True,
                                            check=True)
                    args = json.loads(result.stdout)
                    self.assertEqual(args[0], '-j3')
                    self.assertEqual(env['LEAN_NUM_THREADS'], '3')
                    self.assertTrue(args[1].startswith('-M'))
                    self.assertEqual(args[2:], ['-DautoImplicit=false', 'File.lean'])
                self.assertFalse(wrapper.exists())
            self.assertEqual(lean.read_bytes(), before)

    def test_cached_shortcut_or_one_target_at_a_time(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'A.lean').write_text('import B\n'); (root / 'B.lean').write_text('module\n')
            for codes, expected in [([0], [['lake', '--no-build', 'build', 'A']]),
                                    ([1, 0, 0], [['lake', '--no-build', 'build', 'A'],
                                                 ['lake', 'build', '+B'], ['lake', 'build', '+A']])]:
                with patch.object(build_serial, 'capped_toolchain', return_value=nullcontext({})), \
                        patch.object(build_serial, 'run', side_effect=codes) as run:
                    self.assertEqual(build_serial.build(root, ['A'], root / 'receipts'), 0)
                    self.assertEqual([call.args[0] for call in run.call_args_list], expected)
                    self.assertTrue(all(call.kwargs['budget']['max_active_lean'] == 1
                                        for call in run.call_args_list))


if __name__ == '__main__':
    unittest.main()
