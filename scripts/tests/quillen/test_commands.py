"""Quillen command dispatch, policy binding and cache orchestration."""
from contextlib import redirect_stderr
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.quillen import cache, main, options, resource_config


class CommandTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='quillen-toolkit-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / 'Quillen').mkdir()
        (self.root / 'Quillen.lean').write_text('import Mathlib.Direct\n')

    def test_source_policy_inputs_are_package_implementations(self):
        policy = options(self.root)
        self.assertEqual(policy['production'], ('Quillen',))
        self.assertEqual(policy['check_targets'], ())
        checks = policy['source_checks']
        self.assertEqual(len(checks), 2)
        for check in checks:
            self.assertTrue(Path(check.command[1]).as_posix().endswith('/lean_ci/__main__.py'))
            self.assertIn(str(self.root), check.command)
            self.assertTrue(all(Path(path).is_file() for path in check.inputs))
            self.assertIn('source.py', [Path(path).name for path in check.inputs])
        self.assertIn('generate_imports.py', [Path(path).name for path in checks[0].inputs])
        self.assertNotIn('generate_imports.py', [Path(path).name for path in checks[1].inputs])

    def test_empty_scoped_cache_never_falls_back_to_fetching_all_mathlib(self):
        from lean_ci.quillen import cache
        from types import SimpleNamespace
        with patch.object(cache, 'workspace_imports', return_value=set()), \
                patch.object(cache, 'mathlib_cache_roots', return_value=[]), \
                patch.object(cache.subprocess, 'run', return_value=SimpleNamespace(returncode=0)) as run:
            self.assertEqual(cache.main(['--root', str(self.root)]), 2)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(run.call_args.args[0], ['lake', 'resolve-deps'])

    def test_accepted_resource_variable_names_remain_compatible(self):
        config = resource_config()
        self.assertEqual(config.prefix, 'QUILLEN')
        self.assertEqual(config.profile_keys, ('R5_LEAN_REMOTE_PROFILE',))
        self.assertEqual(config.value({'AGLIB_LEAN_MEMORY_MB': '1024'}, 'memory'), '1024')

    def test_cache_resolution_precedes_scoped_native_fetch(self):
        def resolve(command, **kwargs):
            self.assertEqual(command, ['lake', 'resolve-deps'])
            self.assertEqual(kwargs['cwd'], self.root)
            return subprocess.CompletedProcess(command, 0)
        with patch('lean_ci.quillen.cache.subprocess.run', side_effect=resolve), \
                patch('lean_ci.cli.main', return_value=19) as run, \
                patch.dict(os.environ, QUILLEN_VERIFY_DIR=str(self.root / 'verify')):
            self.assertEqual(cache.main(['--root', str(self.root), '--ci']), 19)
        self.assertEqual(run.call_args.args[0], ['run', '--root', str(self.root), '--receipt',
            str(self.root / 'verify-cache.json'), '--bootstrap-cache', '--',
            'lake', 'exe', 'cache', 'get', 'Mathlib.Direct'])

    def test_failed_resolution_stops_before_fetch(self):
        with patch('lean_ci.quillen.cache.subprocess.run', return_value=subprocess.CompletedProcess([], 23)), \
                patch('lean_ci.cli.main') as run:
            self.assertEqual(cache.main(['--root', str(self.root), '--ci']), 23)
            run.assert_not_called()

    def test_existing_cache_receipt_is_not_overwritten(self):
        receipt = self.root / 'verify-cache.json'
        receipt.write_text('existing')
        with patch('lean_ci.quillen.cache.subprocess.run', return_value=subprocess.CompletedProcess([], 0)), \
                patch('lean_ci.cli.main') as run, \
                patch.dict(os.environ, QUILLEN_VERIFY_DIR=str(self.root / 'verify')), \
                redirect_stderr(io.StringIO()):
            self.assertEqual(cache.main(['--root', str(self.root), '--ci']), 2)
            run.assert_not_called()
        self.assertEqual(receipt.read_text(), 'existing')

    def test_gitless_module_dispatch(self):
        (self.root / 'lakefile.toml').write_text('name = "quillen-k-theory"\ndefaultTargets = ["Quillen"]\n')
        for command in ('layout', 'placeholders'):
            result = subprocess.run([sys.executable, '-m', 'lean_ci', 'quillen', command,
                                     '--root', str(self.root)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
        result = subprocess.run([sys.executable, '-m', 'lean_ci', 'check', '--root',
                                 str(self.root), '--list'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('placeholders', result.stdout)
        self.assertNotIn('AglibTest', result.stdout)
