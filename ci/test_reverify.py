"""Retained native receipt recovery; synthetic execution, no Lean is run."""
import json
import unittest
from unittest.mock import patch

from lean_ci.engine import Application
from lean_ci.state import file_hash
import test_frozen as frozen_fixtures


class ReverificationTests(unittest.TestCase):
    def setUp(self):
        self.fixture = frozen_fixtures.FrozenTests('test_gitless_source_runs_same_runner_and_reuses_exact_success')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)

    def completed_checks_before_failed_final_seal(self):
        with patch.object(Application, 'verify_tasks', side_effect=ValueError('final seal failed')):
            with self.assertRaisesRegex(ValueError, 'final seal failed'):
                self.fixture.run_request()
        self.fixture.executor.calls.clear()
        path = self.fixture.directory / 'state/native.json'
        self.assertEqual(json.loads(path.read_text())['status'], 'running')
        return path

    def test_reverify_runs_no_commands_and_preserves_original_attempt(self):
        path = self.completed_checks_before_failed_final_seal()
        before = file_hash(path)
        result = self.fixture.run_request(verify_only=True)
        self.assertEqual(result['status'], 'succeeded')
        self.assertTrue(result['verification_only'])
        self.assertEqual(result['performed_checks'], [])
        self.assertEqual(result['reused_checks'], ['style'])
        self.assertEqual(result['compiled_or_refreshed_targets'], [])
        self.assertEqual(self.fixture.executor.calls, [])
        self.assertEqual(file_hash(path), before)
        self.assertTrue((path.parent / 'native-verification.json').is_file())

    def test_incomplete_or_bad_receipt_cannot_be_reverified(self):
        path = self.completed_checks_before_failed_final_seal()
        original = json.loads(path.read_text())
        invalid = json.loads(path.read_text())
        invalid['tasks'] = invalid['tasks'][:-1]
        path.write_text(json.dumps(invalid))
        with self.assertRaisesRegex(ValueError, 'coverage is incomplete'):
            self.fixture.run_request(verify_only=True)
        invalid = original
        invalid['tasks'][-1]['result']['success']['receipt']['exit_code'] = 1
        path.write_text(json.dumps(invalid))
        with self.assertRaisesRegex(ValueError, 'individual check success'):
            self.fixture.run_request(verify_only=True)
        self.assertEqual(self.fixture.executor.calls, [])

    def test_new_source_or_compiler_cannot_relabel_old_success(self):
        path = self.completed_checks_before_failed_final_seal()
        original = path.read_text()
        invalid = json.loads(original)
        invalid['toolchain']['lean'] = 'unaccepted-compiler'
        path.write_text(json.dumps(invalid))
        with self.assertRaisesRegex(ValueError, 'compiler/runtime differs'):
            self.fixture.run_request(verify_only=True)
        path.write_text(original)
        self.fixture.request['payload']['changed'] = True
        self.fixture.write_source()
        with self.assertRaisesRegex(ValueError, 'record differs'):
            self.fixture.run_request(verify_only=True)
        self.assertEqual(self.fixture.executor.calls, [])


if __name__ == '__main__':
    unittest.main()
