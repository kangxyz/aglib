"""Compatibility wrappers delegate to shared native helpers; no Lean is run."""
from contextlib import nullcontext
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_serial
import resource_guard


class NativeBuildTests(unittest.TestCase):
    def test_selected_module_build_delegates_arguments_and_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            receipt = root / 'run'
            outputs = root / 'outputs.jsonl'
            with patch('lean_ci.build.build', return_value=19) as native:
                code = build_serial.main(['--root', str(root), '--receipt-dir', str(receipt),
                                          '--rehash', '--outputs', str(outputs), 'Aglib.Example'])
            self.assertEqual(code, 19)
            args, options = native.call_args
            self.assertEqual(args, (root.resolve(), ['Aglib.Example'], receipt))
            self.assertTrue(options['rehash'])
            self.assertEqual(options['outputs'], outputs)
            self.assertEqual(options['selection'], 'module')
            self.assertEqual(options['config'].prefix, 'AGLIB')
            self.assertEqual(options['config'].profile_keys, ('R5_LEAN_REMOTE_PROFILE',))

    def test_resource_command_delegates_guard_without_another_scheduler(self):
        with tempfile.TemporaryDirectory() as directory:
            receipt = Path(directory) / 'command.json'
            with patch('lean_ci.resources.limits', return_value={'max_active_lean': 1}), \
                 patch('lean_ci.resources.run', return_value=19) as native:
                self.assertEqual(resource_guard.main(['--receipt', str(receipt), '--',
                                                       'lake', 'build', '+Aglib.Example']), 19)
            self.assertEqual(native.call_args.args, (['lake', 'build', '+Aglib.Example'],))
            self.assertEqual(native.call_args.kwargs['receipt'], receipt)
            self.assertEqual(native.call_args.kwargs['config'].prefix, 'AGLIB')

    def test_managed_profile_is_passed_to_shared_capped_command(self):
        budget = {'max_active_lean': 3, 'remote_profile': {'jobs': 3}}
        environment = {'LEAN': '/managed/bin/lean'}
        with patch('lean_ci.resources.limits', return_value=budget), \
             patch('lean_ci.build.build_threads', return_value=2), \
             patch('lean_ci.build.capped_toolchain', return_value=nullcontext(environment)) as capped, \
             patch('lean_ci.resources.capped_command', return_value=['/managed/bin/lean', 'Example.lean']), \
             patch('lean_ci.resources.run', return_value=0) as native:
            self.assertEqual(resource_guard.main(['--receipt', '/absolute/receipt.json',
                                                  '--capped-toolchain', '--', 'lean', 'Example.lean']), 0)
        self.assertEqual(capped.call_args.kwargs['threads'], 2)
        self.assertEqual(native.call_args.kwargs['env'], environment)
        self.assertEqual(native.call_args.kwargs['budget']['max_active_lean'], 3)

    def test_bootstrap_mode_rejects_other_commands_before_guard(self):
        with patch('lean_ci.resources.run') as native:
            with self.assertRaises(SystemExit):
                resource_guard.main(['--receipt', '/absolute/receipt.json', '--bootstrap-cache',
                                     '--', 'lake', 'build', 'Aglib'])
        native.assert_not_called()


if __name__ == '__main__':
    unittest.main()
