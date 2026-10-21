"""Fixed audit source admission and data-only module arguments; no Lean runs."""
import json
from pathlib import Path
import tempfile
import unittest

from ci_audit import AUDIT_DRIVER, audit_command, selection_data, validate_driver


ROOT = Path(__file__).resolve().parents[1]


class FixedAuditTests(unittest.TestCase):
    def test_quoted_components_are_data_and_keep_embedded_dots(self):
        value = selection_data(['Aglib.«with.dot».«μ space»', 'AglibTest.AuditCoverage'])
        self.assertEqual(json.loads(value),
                         [['Aglib', 'with.dot', 'μ space'], ['AglibTest', 'AuditCoverage']])

    def test_invalid_selection_cannot_become_an_audit_argument(self):
        invalid = [None, [], 'Aglib.X', [1], [''], ['Aglib.X\nrun_cmd do pure ()'],
                   ['Aglib.«..»'], ['Aglib.«a/b»'], ['Aglib.«a\\b»'],
                   ['Aglib.«line\nbreak»'], ['Aglib.«\x85name»']]
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(ValueError):
                selection_data(value)

    def test_command_runs_the_fixed_file_with_one_json_data_argument(self):
        command = audit_command(ROOT, ['AglibTest.AuditCoverage'])
        self.assertEqual(command[:-1], ['lake', 'env', 'lean', '-j1', '--run', AUDIT_DRIVER])
        self.assertEqual(json.loads(command[-1]), [['AglibTest', 'AuditCoverage']])

    def test_changed_driver_bytes_are_rejected_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / AUDIT_DRIVER
            target.parent.mkdir(parents=True)
            target.write_bytes((ROOT / AUDIT_DRIVER).read_bytes() + b'\n-- different driver\n')
            with self.assertRaisesRegex(ValueError, 'unreviewed fixed audit driver'):
                audit_command(root, ['AglibTest.AuditCoverage'])

    def test_missing_driver_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory, self.assertRaises(OSError):
            validate_driver(Path(directory))


if __name__ == '__main__':
    unittest.main()
