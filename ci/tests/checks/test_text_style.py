"""Pinned Python text-style compatibility and common style stage ordering."""
import ast
import contextlib
from hashlib import sha256
import io
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.checks import native, text_style


class TextStyleInterfaceTests(unittest.TestCase):
    def test_vendor_hash_and_exact_repair_sites_are_required(self):
        with self.assertRaisesRegex(ValueError, 'unsupported lint-style.py SHA256'):
            text_style.patched_source(b'unrecognized vendor')
        raw = b'no repair sites'
        with patch.object(text_style, 'EXPECTED_SHA256', sha256(raw).hexdigest()):
            with self.assertRaisesRegex(ValueError, 'exactly one repair site'):
                text_style.patched_source(raw)
        with self.assertRaisesRegex(ValueError, '--fix'):
            text_style.run(Path('unused'), [Path('--fix')])

    def test_checker_inputs_bind_common_module_and_actual_vendor(self):
        root = Path('/consumer')
        inputs = native.checker_inputs('style', root=root)
        self.assertIn(Path(text_style.__file__), inputs)
        self.assertIn(root / '.lake/packages/mathlib/scripts/lint-style.py', inputs)

    def test_python_failure_stops_before_any_lean_discovery(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Fixture.lean').write_text('example : True := by trivial\n')
            with patch.object(text_style, 'run', return_value=1) as run, \
                 patch.object(native, 'lake_environment') as environment, \
                 patch.object(native.subprocess, 'run') as process, \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(native.run_style(root, ['Fixture']), 1)
                run.assert_called_once_with(root / '.lake/packages/mathlib/scripts/lint-style.py',
                                            [root / 'Fixture.lean'])
                environment.assert_not_called()
                process.assert_not_called()

    def test_python_success_precedes_lean_runtime_discovery(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Fixture.lean').write_text('example : True := by trivial\n')
            with patch.object(text_style, 'run', return_value=0) as run, \
                 patch.object(native, 'lake_environment', side_effect=RuntimeError('Lean phase reached')) as environment:
                with self.assertRaisesRegex(RuntimeError, 'Lean phase reached'):
                    native.run_style(root, ['Fixture'])
                run.assert_called_once()
                environment.assert_called_once_with(root)


class PinnedTextStyleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = os.environ.get('LEAN_CI_NATIVE_TEST_ROOT')
        if not root:
            raise unittest.SkipTest('pinned vendor prerequisite missing: set LEAN_CI_NATIVE_TEST_ROOT')
        cls.vendor = Path(root).resolve() / '.lake/packages/mathlib/scripts/lint-style.py'
        if not cls.vendor.is_file():
            raise unittest.SkipTest('pinned Mathlib lint-style.py source prerequisite missing')

    def test_extant_rules_keep_vendor_diagnostics_and_sources_read_only(self):
        fixtures = {
            'Good.lean': ('theorem good : True := by\n  trivial\n', 0, None),
            'Indent.lean': ('theorem bad_indent\n  (n : Nat) : n = n := rfl\n', 1, 'ERR_IND'),
            'By.lean': ('theorem bad_by : True :=\nby\n  trivial\n', 1, 'ERR_IBY'),
            'Arrow.lean': ('def bad_arrow := do\n  let n ←pure 1\n  pure n\n', 1, 'ERR_ARR'),
        }
        before = self.vendor.read_bytes()
        argv = sys.argv
        with tempfile.TemporaryDirectory() as directory:
            for name, (content, status, diagnostic) in fixtures.items():
                with self.subTest(name=name):
                    source = Path(directory) / name
                    source.write_text(content)
                    with contextlib.redirect_stdout(io.StringIO()) as output:
                        self.assertEqual(text_style.run(self.vendor, [source]), status)
                    if diagnostic:
                        self.assertIn(diagnostic, output.getvalue())
                    else:
                        self.assertEqual(output.getvalue(), '')
                    self.assertEqual(source.read_text(), content)
                    self.assertIs(sys.argv, argv)
        self.assertEqual(self.vendor.read_bytes(), before)

    def test_repaired_vendor_runs_exactly_the_three_retained_functions(self):
        source = text_style.patched_source(self.vendor.read_bytes())
        tree = ast.parse(source)
        calls = [node for node in ast.walk(tree) if isinstance(node, ast.For)
                 and isinstance(node.target, ast.Name) and node.target.id == 'error_check']
        self.assertEqual(len(calls), 1)
        self.assertEqual([value.id for value in calls[0].iter.elts],
                         ['four_spaces_in_second_line', 'isolated_by_dot_semicolon_check', 'left_arrow_check'])


if __name__ == '__main__':
    unittest.main()
