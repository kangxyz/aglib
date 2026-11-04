# Authors: kangxyz
"""Aglib source discovery, import parsing, and topic generation."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from lean_tools.source import is_import_surface, lean_imports, module_path, source_modules
from lean_tools.imports import generate_topic
from lean_tools.library import PROFILES

GENERATED_MARKER = PROFILES['aglib']['generated_marker']
LEGACY_GENERATED_MARKER = PROFILES['aglib']['generated_markers'][-1]

HEADER = 'module\npublic import Mathlib.Data.Nat.Basic\n@[expose] public section\n'


class ImportDiscoveryTests(unittest.TestCase):
    def test_native_test_discovery_needs_no_umbrella(self):
        with tempfile.TemporaryDirectory(prefix='aglib-source-discovery-') as directory:
            root = Path(directory)
            test_module = root / 'AglibTest/Positive.lean'
            test_module.parent.mkdir()
            test_module.write_text(HEADER)
            roots = ('AglibTest',)
            self.assertEqual(set(source_modules(root, roots)), {'AglibTest.Positive'})
            (root / 'AglibTest.lean').write_text('import AglibTest.Positive\n')
            self.assertEqual(set(source_modules(root, roots)), {'AglibTest', 'AglibTest.Positive'})

    def test_parser_nested_comments_strings_quoted_roots_import_all(self):
        text = '''/- import R5Lab.Fake /- nested -/ -/
module
meta import /- between -/ all «Aglib».Algebra.A
public import
  Aglib.Algebra.B
import Mathlib.Data.Nat.Basic
#check "import Quillen.Fake"
'''
        self.assertEqual(lean_imports(text), ['Aglib.Algebra.A',
                         'Aglib.Algebra.B', 'Mathlib.Data.Nat.Basic'])
        self.assertEqual(module_path('Aglib.«A.B»'),
                         Path('Aglib/A.B.lean'))

    def test_import_header_stops_before_run_cmd_negative_control(self):
        source = ('import AglibTest.AuditSupport\n'
                  'import AglibTest.NegativeControls.ImportedFixture\n\n'
                  'run_cmd do\n  let count ← AglibAudit.auditModules #[]\n')
        self.assertEqual(lean_imports(source),
                         ['AglibTest.AuditSupport',
                          'AglibTest.NegativeControls.ImportedFixture'])
        self.assertFalse(is_import_surface(source))

    def test_one_module_directives_stop_at_unknown_command_without_keyword_list(self):
        source = ('module\npublic import Aglib.Algebra.A\n'
                  'generate_audit_declarations\n')
        self.assertEqual(lean_imports(source), ['Aglib.Algebra.A'])
        self.assertFalse(is_import_surface(source))

    def test_header_imports_can_share_a_line_and_do_not_scan_body_quotations(self):
        source = ('import Aglib.Algebra.A import Aglib.Algebra.B\n'
                  'def syntaxValue := `(command|\n import Quillen.Fake\n)\n')
        self.assertEqual(lean_imports(source), ['Aglib.Algebra.A', 'Aglib.Algebra.B'])


class TopicGenerationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='aglib-topic-generation-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.directory = self.root / 'Aglib/NewFamily'
        self.directory.mkdir(parents=True)
        self.leaf = self.directory / 'First.lean'
        self.leaf.write_text(HEADER + 'def first : Nat := 1\n')
        self.native_root = self.root / 'Aglib.lean'
        self.native_root.write_text('module\n')
        self.facade = self.root / 'Aglib/NewFamily.lean'

    def test_new_topic_gets_exemption_and_keeps_it_after_growth(self):
        self.assertEqual(generate_topic(self.root, 'Aglib.NewFamily'), Path('Aglib/NewFamily.lean'))
        first = self.facade.read_text()
        self.assertIn(GENERATED_MARKER, first)
        self.assertIn('set_option linter.style.longFile 0\n', first)
        self.assertEqual(lean_imports(first), ['Aglib.NewFamily.First'])
        (self.directory / 'Second.lean').write_text(HEADER)
        generate_topic(self.root, 'Aglib.NewFamily')
        grown = self.facade.read_text()
        self.assertEqual(lean_imports(grown), ['Aglib.NewFamily.First', 'Aglib.NewFamily.Second'])
        self.assertEqual(grown.count('set_option linter.style.longFile 0'), 1)
        self.assertTrue(is_import_surface(grown))
        self.assertEqual(self.native_root.read_text(), 'module\n')
        self.assertEqual(self.leaf.read_text(), HEADER + 'def first : Nat := 1\n')

    def test_nested_new_topic_needs_no_registry_entry(self):
        nested = self.directory / 'Nested'
        nested.mkdir()
        (nested / 'Leaf.lean').write_text(HEADER)
        generate_topic(self.root, 'Aglib.NewFamily.Nested')
        source = nested.with_suffix('.lean').read_text()
        self.assertEqual(lean_imports(source), ['Aglib.NewFamily.Nested.Leaf'])
        self.assertIn('set_option linter.style.longFile 0', source)

    def test_legacy_owned_entry_preserves_credits_and_retires_finite_limit(self):
        prefix = ('/-\nCopyright (c) 2026 Original contributors.\n'
                  'Released under Apache 2.0 license as described in the file LICENSE.\n'
                  'Authors: Original Author\n-/\n\n')
        self.facade.write_text(prefix + LEGACY_GENERATED_MARKER + 'module\n'
                              'public import Aglib.NewFamily.First\n'
                              'set_option linter.style.longFile 3100\n')
        generate_topic(self.root, 'Aglib.NewFamily')
        source = self.facade.read_text()
        self.assertTrue(source.startswith(prefix + GENERATED_MARKER))
        self.assertIn('set_option linter.style.longFile 0', source)
        self.assertNotIn('3100', source)

    def test_manual_and_mislabelled_implementation_entries_are_preserved(self):
        for original in ('module\npublic import Aglib.NewFamily.First\n',
                         GENERATED_MARKER + HEADER + 'def answer := 42\n'):
            with self.subTest(original=original):
                self.facade.write_text(original)
                with self.assertRaisesRegex(ValueError, 'manually owned or non-import-only|contains implementation commands'):
                    generate_topic(self.root, 'Aglib.NewFamily')
                self.assertEqual(self.facade.read_text(), original)

    def test_native_root_tests_and_missing_topics_are_not_generated(self):
        for name in ('Aglib', 'AglibTest.NewFamily', 'Aglib.Missing', '../Outside'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                generate_topic(self.root, name)
        self.assertFalse(self.facade.exists())
        self.assertEqual(self.native_root.read_text(), 'module\n')

    def test_cycle_is_rejected_before_writing(self):
        self.leaf.write_text('module\npublic import Aglib.NewFamily\n')
        with self.assertRaisesRegex(ValueError, 'Generated facade import cycle'):
            generate_topic(self.root, 'Aglib.NewFamily')
        self.assertFalse(self.facade.exists())

    def test_actual_cli_generates_only_when_explicitly_requested(self):
        result = subprocess.run([sys.executable, '-B', '-m', 'lean_tools', 'imports', '--root', str(self.root),
                                 '--generate', 'Aglib.NewFamily'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(self.facade.is_file())
        self.assertIn('set_option linter.style.longFile 0', self.facade.read_text())


if __name__ == '__main__':
    unittest.main()
