"""The unified CLI preserves native arguments, environment and resource ownership."""
from contextlib import nullcontext
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from lean_tools.cli import main


class ToolkitCliTests(unittest.TestCase):
    def package(self, directory):
        root = Path(directory)
        (root / 'lakefile.toml').write_text('name = "Aglib"\ndefaultTargets = ["Aglib"]\n')
        return root

    def test_selected_module_build_preserves_failure_and_managed_options(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.package(directory)
            with patch('lean_tools.build.build', return_value=19) as build:
                self.assertEqual(main(['build', '--root', directory, '--receipt-dir', str(root / 'run'),
                    '--outputs', str(root / 'outputs.jsonl'), 'Aglib.Example']), 19)
            self.assertEqual(build.call_args.args, (root.resolve(), ['Aglib.Example'], (root / 'run').resolve()))
            self.assertEqual(build.call_args.kwargs['config'].prefix, 'AGLIB')
            self.assertTrue(build.call_args.kwargs['rehash'])

    def test_run_uses_the_shared_resource_implementation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.package(directory)
            with patch('lean_tools.resources.limits', return_value={'max_active_lean': 1}), \
                 patch('lean_tools.resources.run', return_value=19) as run:
                self.assertEqual(main(['run', '--root', directory, '--receipt', str(root / 'r.json'),
                    '--', 'lake', 'build', '+Aglib.Example']), 19)
            self.assertEqual(run.call_args.args, (['lake', 'build', '+Aglib.Example'],))
            self.assertEqual(run.call_args.kwargs['config'].prefix, 'AGLIB')

    def test_bootstrap_accepts_scoped_native_cache_and_preserves_managed_admission(self):
        budget = {'max_active_lean': 3, 'remote_profile': {'jobs': 3}}
        environment = {'LEAN': '/managed/bin/lean', 'PYTHONPATH': '/existing/profile'}
        with tempfile.TemporaryDirectory() as directory:
            self.package(directory)
            with patch('lean_tools.resources.limits', return_value=budget), \
                 patch('lean_tools.build.build_threads', return_value=4), \
                 patch('lean_tools.build.capped_toolchain', return_value=nullcontext(environment)) as capped, \
                 patch('lean_tools.resources.run', return_value=0) as run:
                self.assertEqual(main(['run', '--root', directory, '--receipt', '/tmp/cache.json',
                    '--bootstrap-cache', '--', 'lake', 'exe', 'cache', 'get', 'Mathlib.Data.Nat.Basic'],
                    environment=environment), 0)
            self.assertEqual(capped.call_args.args[1], 4)
            self.assertEqual(run.call_args.kwargs['budget']['max_active_lean'], 3)
            self.assertEqual(run.call_args.kwargs['env'], environment)

    def test_bootstrap_rejects_an_unrelated_command_before_launch(self):
        with tempfile.TemporaryDirectory() as directory:
            self.package(directory)
            with patch('lean_tools.resources.run') as run:
                self.assertEqual(main(['run', '--root', directory, '--receipt', '/tmp/cache.json',
                    '--bootstrap-cache', '--', 'lake', 'build', 'Aglib']), 1)
            run.assert_not_called()

    def test_source_only_cannot_report_success_with_no_selected_source_policy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lakefile.toml').write_text('name = "Other"\ndefaultTargets = ["Other"]\n')
            with patch('lean_tools.local.check') as check:
                self.assertEqual(main(['check', '--root', directory, '--source-only']), 1)
            check.assert_not_called()

    def test_check_does_not_rebind_the_native_python_environment(self):
        with tempfile.TemporaryDirectory() as directory:
            self.package(directory)
            environment = {'PYTHONPATH': '/accepted/remote/profile', 'AGLIB_BUILD_THREADS': '4'}
            with patch('lean_tools.local.check', return_value={'status': 'complete'}) as check:
                self.assertEqual(main(['check', '--root', directory], environment=environment), 0)
            self.assertEqual(check.call_args.kwargs['environment'], environment)
            self.assertEqual(check.call_args.kwargs['production'] if 'production' in check.call_args.kwargs
                             else check.call_args.args[1], ['Aglib'])


if __name__ == '__main__':
    unittest.main()
