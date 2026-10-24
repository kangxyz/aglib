#!/usr/bin/env python3
"""Check placeholder scan coverage and lexical false positives."""
from pathlib import Path
import tempfile
import unittest

from lean_tools.quillen.check_placeholders import check_placeholders


class PlaceholderTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-tokens-')
        self.root = Path(self.tmp.name)
        (self.root / 'Quillen').mkdir()
        (self.root / 'Quillen.lean').write_text('')

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, path, content):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)

    def test_comments_and_strings_ignored_but_real_placeholder_rejected(self):
        self.write('Quillen/Example.lean', '''/- sorry /- axiom -/ admit -/
def s := "sorry and axiom with \\" quote"
example : True := by
  sorry
''')
        errors = check_placeholders(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn('Quillen/Example.lean:4: forbidden token sorry', errors[0])

    def test_core_test_and_independent_client_all_scanned(self):
        self.write('Quillen/Bad.lean', 'axiom bad : False\n')
        self.write('QuillenTest.lean', '')
        self.write('QuillenTest/Bad.lean', 'example : True := by admit\n')
        self.write('examples/downstream/Consumer/Bad.lean', 'example : True := by sorry\n')
        errors = check_placeholders(self.root)
        self.assertEqual(len(errors), 3)
        self.assertTrue(any('QuillenTest/Bad.lean' in error for error in errors))
        self.assertTrue(any('Consumer/Bad.lean' in error for error in errors))

    def test_downstream_dependency_cache_is_not_scanned(self):
        self.write('examples/downstream/.lake/packages/Dep/Bad.lean', 'sorry\n')
        self.assertEqual(check_placeholders(self.root), [])


if __name__ == '__main__':
    unittest.main()
