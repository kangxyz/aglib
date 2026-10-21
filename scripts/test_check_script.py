"""Check the shared local-entry forwarder and failure propagation without native work."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('check.sh')


class CheckScriptTests(unittest.TestCase):
    def run_script(self, failure='', *args, full=True):
        with tempfile.TemporaryDirectory(prefix='ag-check-script-') as temp:
            root = Path(temp)
            scripts = root / 'scripts'
            scripts.mkdir()
            (scripts / 'check.sh').write_bytes(SCRIPT.read_bytes())
            (root / 'examples/downstream').mkdir(parents=True)
            binary = root / 'bin'
            binary.mkdir()
            log = root / 'commands'
            for command in ['python3', 'lake']:
                executable = binary / command
                executable.write_text('#!/usr/bin/env bash\n'
                    'printf "%s\\n" "$(basename "$0") $*" >> "$CHECK_TEST_LOG"\n'
                    'if [[ -n "$CHECK_TEST_FAILURE" && "$*" == *"$CHECK_TEST_FAILURE"* ]]; then\n'
                    '  exit 19\nfi\nexit 0\n')
                executable.chmod(0o755)
            env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ['PATH'],
                       CHECK_TEST_LOG=str(log), CHECK_TEST_FAILURE=failure)
            result = subprocess.run(['bash', str(scripts / 'check.sh'), *(['--full'] if full else []), *args], env=env,
                                    capture_output=True, text=True)
            return result.returncode, log.read_text() if log.exists() else ''

    def test_default_routes_to_incremental_adapter_with_explicit_baseline(self):
        code, log = self.run_script('', '--base', 'accepted', '--ci', full=False)
        self.assertEqual(code, 0)
        self.assertIn('scripts/check_affected.py --base accepted --ci', log)
        self.assertNotIn('generate_imports.py', log)
        self.assertNotIn('Aglib AglibTest', log)

    def test_full_scope_forwards_to_the_same_recipe(self):
        for args in [('--rehash',), ('--rehash', '--ci')]:
            with self.subTest(args=args):
                code, log = self.run_script('', *args)
                self.assertEqual(code, 0)
                self.assertEqual(len(log.splitlines()), 1)
                self.assertIn('scripts/check_affected.py --full ' + ' '.join(args), log)
                for duplicate_stage in ('build_serial.py', 'prepare_downstream.py',
                                        'check_kernel.py', 'check_negative_controls.py',
                                        'check_compiled_inventory.py', 'Audits/Aglib.lean'):
                    self.assertNotIn(duplicate_stage, log)

    def test_source_only_is_forwarded_without_separate_shell_builds(self):
        code, log = self.run_script('', '--source-only')
        self.assertEqual(code, 0)
        self.assertIn('scripts/check_affected.py --full --source-only', log)
        self.assertEqual(len(log.splitlines()), 1)
        self.assertNotIn('lake ', log)

    def test_adapter_failure_propagates_without_shell_retry(self):
        for full in (False, True):
            with self.subTest(full=full):
                code, log = self.run_script('scripts/check_affected.py', '--ci', full=full)
                self.assertEqual(code, 19)
                self.assertEqual(len(log.splitlines()), 1)

    def test_shell_runs_from_its_own_package_root(self):
        source = SCRIPT.read_text()
        self.assertIn('cd "$(dirname "$0")/.."', source)
        self.assertIn('exec python3 scripts/check_affected.py "$@"', source)


if __name__ == '__main__':
    unittest.main()
