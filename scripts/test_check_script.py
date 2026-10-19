"""Check fail propagation and explicit audit/kernel replay with controlled commands."""
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

    def test_source_only_never_builds(self):
        code, log = self.run_script('', '--source-only')
        self.assertEqual(code, 0)
        self.assertNotIn('lake ', log)
        self.assertIn('check_source_policy.py', log)

    def test_source_guard_failure_stops_dependents(self):
        code, log = self.run_script('check_library_layout.py')
        self.assertEqual(code, 19)
        self.assertNotIn('check_placeholders.py', log)
        self.assertNotIn('lake ', log)

    def test_audit_failure_stops_negative_and_kernel_replay(self):
        code, log = self.run_script('AglibTest/Axioms.lean')
        self.assertEqual(code, 19)
        self.assertNotIn('check_negative_controls.py', log)
        self.assertNotIn('check_kernel.py', log)

    def test_full_check_replays_audit_and_scoped_kernel(self):
        code, log = self.run_script('', '--rehash')
        self.assertEqual(code, 0)
        self.assertIn('build_serial.py --receipt-dir', log)
        self.assertIn('--rehash Aglib AglibTest', log)
        self.assertIn('lake env lean -j1 AglibTest/Axioms.lean', log)
        self.assertIn('check_kernel.py --receipt-dir', log)
        self.assertIn('check_kernel.py --root', log)
        self.assertIn('--client', log)
        self.assertIn('resource_guard.py --capped-toolchain', log)
        self.assertIn('lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Aglib', log)
        self.assertIn('python3 scripts/run_style_linter.py', log)
        self.assertNotIn('lake --rehash lint', log)
        self.assertNotIn('exe lint-style', log)
        self.assertEqual(log.count('check_kernel.py'), 2)

    def test_ci_omits_only_additional_independent_kernel_replays(self):
        code, log = self.run_script('', '--rehash', '--ci')
        self.assertEqual(code, 0)
        for stage in ['build_serial.py', '--rehash Aglib AglibTest', 'lake --rehash test',
                      'lake --rehash lint -- --no-build',
                      'lake --rehash exe mathlib/lint-style Aglib AglibTest',
                      'AglibTest/Axioms.lean', 'check_negative_controls.py',
                      'check_compiled_inventory.py', 'prepare_downstream.py',
                      '--rehash Consumer', 'Audit.lean']:
            self.assertIn(stage, log)
        self.assertNotIn('check_kernel.py', log)
        self.assertNotIn('batteries/scripts/runLinter.lean', log)
        self.assertNotIn('run_style_linter.py', log)

    def test_ci_native_declaration_linter_failure_stops_dependents(self):
        code, log = self.run_script('lint -- --no-build', '--ci')
        self.assertEqual(code, 19)
        self.assertNotIn('exe mathlib/lint-style', log)
        self.assertNotIn('AglibTest/Axioms.lean', log)

    def test_ci_native_style_failure_stops_audits(self):
        code, log = self.run_script('exe mathlib/lint-style', '--ci')
        self.assertEqual(code, 19)
        self.assertNotIn('AglibTest/Axioms.lean', log)
        self.assertNotIn('check_kernel.py', log)

    def test_declaration_linter_failure_stops_style_and_audits(self):
        code, log = self.run_script('batteries/scripts/runLinter.lean')
        self.assertEqual(code, 19)
        self.assertNotIn('run_style_linter.py', log)
        self.assertNotIn('AglibTest/Axioms.lean', log)

    def test_style_linter_failure_stops_audits(self):
        code, log = self.run_script('run_style_linter.py')
        self.assertEqual(code, 19)
        self.assertNotIn('AglibTest/Axioms.lean', log)
        self.assertNotIn('check_kernel.py', log)


if __name__ == '__main__':
    unittest.main()
