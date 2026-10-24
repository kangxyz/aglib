#!/usr/bin/env python3
"""Exercise Lean import scanning and dynamically discovered import surfaces."""
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

from lean_tools.imports import (
    GENERATED_MARKER, generated_files, render_imports, stale_files,
    source_authors,
)
from lean_tools.source import (
    is_import_surface, lean_imports, module_path,
)
from functools import partial
from lean_tools.library import PROFILES
COPYRIGHT_HEADER = PROFILES['quillen']['copyright_header']
render_imports = partial(render_imports, data=PROFILES['quillen'])


def project_imports(text):
    return [name for name in lean_imports(text) if name == 'Quillen' or name.startswith('Quillen.')]



class ImportParserTests(unittest.TestCase):
    def test_pinned_header_grammar_and_quoted_names(self):
        source = ('/- import Quillen.Hidden -/ module\n'
                  'public meta import all «Quillen».A\n'
                  'import\n Quillen.B\n'
                  'def text := "import Quillen.Hidden"\n'
                  'import Quillen.NotInHeader\n')
        self.assertEqual(lean_imports(source), ['Quillen.A', 'Quillen.B'])
        self.assertEqual([name for name in lean_imports(source) if name == 'Quillen' or name.startswith('Quillen.')], ['Quillen.A', 'Quillen.B'])
        self.assertEqual(module_path('Quillen.«A.B»'), Path('Quillen/A.B.lean'))

    def test_strings_terminate_import_token_scan(self):
        self.assertEqual(lean_imports('import Quillen.A\n#check "x"\nQuillen.NotAnImport\n'),
                         ['Quillen.A'])

    def test_modern_import_all_does_not_become_a_fake_module(self):
        source = '''module
public meta import /- comment -/ all Quillen.A
import all
  Quillen.B
public import Mathlib.Data.Nat.Basic
'''
        self.assertEqual(lean_imports(source),
                         ['Quillen.A', 'Quillen.B', 'Mathlib.Data.Nat.Basic'])


class ImportGenerationTests(unittest.TestCase):
    @staticmethod
    def header(authors):
        return COPYRIGHT_HEADER.replace('Authors: Quillen K-theory contributors',
                                        'Authors: ' + authors)

    def test_authors_only_come_from_initial_copyright_header(self):
        header = self.header(' Alice, Bob, Alice , , Élodie ')
        body = '/- Authors: Body Credit -/\ndef s := "Authors: String Credit"\n'
        self.assertEqual(source_authors(header + body), {'Alice', 'Bob', 'Élodie'})
        for source in (body, '/- ordinary comment\nAuthors: Nobody\n-/\n',
                       '-- preface\n' + header, header.replace('-/', ''),
                       COPYRIGHT_HEADER.replace('Authors:', 'Other:') + body):
            with self.subTest(source=source):
                self.assertEqual(source_authors(source), set())

    def test_facade_size_exemption_survives_growth_without_losing_imports(self):
        modules = [f'Quillen.Future.M{i:04d}' for i in range(1600)]
        for size in (1, 1600):
            source = render_imports(modules[:size], '# Future import surface', modern=True)
            self.assertEqual(lean_imports(source), modules[:size])
            self.assertEqual(source.count('set_option linter.style.longFile 0'), 1)
            self.assertTrue(is_import_surface(source))
            self.assertFalse(is_import_surface(source + '\ndef datum : Nat := 0\n'))

    def test_long_import_wraps_without_disabling_line_lint(self):
        name = 'Quillen.' + '.'.join(['LongSubject'] * 7)
        source = render_imports([name], '# Long import', modern=True)
        self.assertEqual(lean_imports(source), [name])
        self.assertTrue(is_import_surface(source))
        self.assertTrue(all(len(line) <= 100 for line in source.splitlines()))
        self.assertNotIn('set_option linter.style.longLine', source)

    def test_module_name_width_boundary_keeps_complete_import_lines(self):
        for modern in (False, True):
            prefix = 'public import ' if modern else 'import '
            for width in (98, 99, 100, 101):
                name = 'Quillen.' + 'A' * (width - len('Quillen.'))
                with self.subTest(modern=modern, width=width):
                    source = render_imports([name], '# Width boundary', modern=modern)
                    self.assertEqual(lean_imports(source), [name])
                    self.assertTrue(is_import_surface(source))
                    if width == 98:
                        self.assertIn(prefix.rstrip() + '\n  ' + name + '\n', source)
                    else:
                        self.assertIn(prefix + name + '\n', source)
                        self.assertNotIn(prefix.rstrip() + '\n', source)
                    self.assertNotIn('set_option linter.style.longLine', source)

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-generation-')
        self.root = Path(self.tmp.name)
        for module in ('Quillen/Algebra/Z.lean', 'Quillen/Algebra/A.lean',
                       'Quillen/Scheme.lean', 'Quillen/Resolution.lean',
                       'Quillen/Library.lean', 'Quillen/Examples/Client.lean'):
            path = self.root / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('-- fixture\n')
        (self.root / 'Quillen.lean').write_text('')

    def tearDown(self):
        self.tmp.cleanup()

    def generate(self):
        for path, content in generated_files(self.root).items():
            (self.root / path).write_text(content)

    def test_native_roots_are_untouched_while_thematic_and_client_generation_remains(self):
        native = 'import Quillen.Algebra\n'
        (self.root / 'Quillen.lean').write_text(native)
        tests = self.root / 'QuillenTest'
        tests.mkdir()
        (tests / 'Positive.lean').write_text('import Quillen.Algebra.A\n')
        client = self.root / 'examples/downstream/Consumer'
        client.mkdir(parents=True)
        (client / 'Leaf.lean').write_text('module\npublic import Quillen.Algebra.A\n')
        outputs = generated_files(self.root)
        self.assertNotIn(Path('Quillen.lean'), outputs)
        self.assertNotIn(Path('QuillenTest.lean'), outputs)
        self.assertIn(Path('Quillen/Algebra.lean'), outputs)
        self.assertIn(Path('examples/downstream/Consumer.lean'), outputs)
        self.generate()
        self.assertEqual((self.root / 'Quillen.lean').read_text(), native)
        self.assertFalse((self.root / 'QuillenTest.lean').exists())

    def test_readme_only_candidate_family_waits_for_enrolled_lean_source(self):
        self.generate()
        baseline = generated_files(self.root)
        directory = self.root / 'Quillen/Future/Candidate'
        directory.mkdir(parents=True)
        (directory / 'README.md').write_text('Future candidates; no implementation enrolled.\n')
        self.assertEqual(generated_files(self.root), baseline)
        self.assertEqual(stale_files(self.root), [])
        self.assertFalse((self.root / 'Quillen/Future.lean').exists())
        (directory / 'Leaf.lean').write_text('')
        outputs = generated_files(self.root)
        self.assertEqual(project_imports(outputs[Path('Quillen/Future.lean')]),
                         ['Quillen.Future.Candidate.Leaf'])
        self.assertNotIn(Path('Quillen.lean'), outputs)

    def test_new_family_requires_generation_without_registry_edit(self):
        self.generate()
        path = self.root / 'Quillen/Future/Deep/New.lean'
        path.parent.mkdir(parents=True)
        path.write_text('')
        self.assertEqual(set(stale_files(self.root)),
                         {Path('Quillen/Future.lean')})
        self.generate()
        self.assertEqual(stale_files(self.root), [])
        source = (self.root / 'Quillen/Future.lean').read_text()
        self.assertIn('Quillen.Future.Deep.New', [name for name in lean_imports(source) if name == 'Quillen' or name.startswith('Quillen.')])
        self.assertIn('set_option linter.style.longFile 0', source)

    def test_new_leaf_and_removed_leaf_stale(self):
        self.generate()
        leaf = self.root / 'Quillen/Algebra/New.lean'
        leaf.write_text('')
        self.assertEqual(set(stale_files(self.root)),
                         {Path('Quillen/Algebra.lean')})
        self.generate()
        leaf.unlink()
        self.assertTrue(stale_files(self.root))

    def test_generator_preserves_hand_owned_files_and_implementations(self):
        (self.root / 'Quillen/Algebra/A.lean').write_bytes(
            (self.header('Original Author, Future Author') + 'def datum := 1\n')
            .replace('\n', '\r\n').encode())
        originals = {path: path.read_bytes() for path in self.root.rglob('*.lean')
                     if path.name != 'Quillen.lean'}
        self.generate()
        self.generate()
        self.assertTrue(all(path.read_bytes() == content for path, content in originals.items()))

    def test_source_contributors_are_scoped_deduplicated_and_sorted(self):
        (self.root / 'Quillen/Algebra/A.lean').write_text(self.header('Zoe, Alice, Zoe'))
        (self.root / 'Quillen/Algebra/Z.lean').write_text(self.header(' Bob , Alice'))
        # A manually maintained facade remains a credited source at the root.
        (self.root / 'Quillen/Scheme.lean').write_text(self.header('Manual Author'))
        tests = self.root / 'QuillenTest'
        tests.mkdir()
        (tests / 'Axioms.lean').write_text(self.header('Test Author, Alice'))
        original_test = (tests / 'Axioms.lean').read_bytes()
        outputs = generated_files(self.root)
        self.assertEqual(source_authors(outputs[Path('Quillen/Algebra.lean')]),
                         {'Alice', 'Bob', 'Zoe'})
        self.assertIn('Authors: Alice, Bob, Zoe\n', outputs[Path('Quillen/Algebra.lean')])
        self.assertNotIn(Path('Quillen.lean'), outputs)
        self.assertNotIn(Path('QuillenTest.lean'), outputs)
        self.generate()
        self.assertEqual((tests / 'Axioms.lean').read_bytes(), original_test)
        self.assertEqual(generated_files(self.root), outputs)

    def test_new_contributor_survives_regeneration_without_generated_feedback(self):
        leaf = self.root / 'Quillen/Algebra/A.lean'
        leaf.write_text(self.header('Original Author'))
        self.generate()
        # Stale top-level, nested, root, and test surfaces must not seed authors.
        nested = self.root / 'Quillen/Algebra/Nested'
        nested.mkdir()
        (nested / 'Leaf.lean').write_text(self.header('Nested Author'))
        stale = self.header('Stale Generated Author') + GENERATED_MARKER
        nested.with_suffix('.lean').write_text(stale)
        (self.root / 'Quillen/Algebra.lean').write_text(stale)
        (self.root / 'Quillen.lean').write_text(stale)
        tests = self.root / 'QuillenTest'
        tests.mkdir()
        (tests / 'Actual.lean').write_text(self.header('Test Author'))
        (tests / 'OldFacade.lean').write_text(stale)
        (self.root / 'QuillenTest.lean').write_text(stale)
        leaf.write_text(self.header('Original Author, New Contributor'))
        original = leaf.read_bytes()
        self.generate()
        self.generate()
        self.assertEqual(leaf.read_bytes(), original)
        for path in ('Quillen/Algebra.lean',):
            self.assertEqual(source_authors((self.root / path).read_text()),
                             {'Original Author', 'New Contributor', 'Nested Author'})
        self.assertEqual(source_authors(nested.with_suffix('.lean').read_text()),
                         {'Nested Author'})
        self.assertEqual((self.root / 'QuillenTest.lean').read_text(), stale)
        self.assertEqual((self.root / 'Quillen.lean').read_text(), stale)
        self.assertEqual(stale_files(self.root), [])

    def test_headerless_fixtures_keep_neutral_fallback_and_render_api(self):
        outputs = generated_files(self.root)
        self.assertTrue(all(source.startswith(COPYRIGHT_HEADER + GENERATED_MARKER)
                            for source in outputs.values()))
        self.assertTrue(render_imports([], '# Empty').startswith(COPYRIGHT_HEADER))

    def test_cli_preserves_manual_future_facade_and_enrolls_its_family(self):
        directory = self.root / 'Quillen/Future'
        directory.mkdir()
        (directory / 'Leaf.lean').write_text('-- future implementation\n')
        facade = self.root / 'Quillen/Future.lean'
        original = b'import Quillen.Future.Leaf\n\ndef futureAnswer : Nat := 42\n'
        facade.write_bytes(original)
        # A marker mentioned elsewhere does not transfer ownership.
        facade.write_bytes(original + ('-- ' + GENERATED_MARKER).encode())
        original = facade.read_bytes()
        result = subprocess.run([sys.executable, '-m', 'lean_tools', 'imports', '--root', str(self.root)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(facade.read_bytes(), original)
        self.assertNotIn(Path('Quillen/Future.lean'), generated_files(self.root))
        self.assertEqual(stale_files(self.root), [])
        root_imports = project_imports((self.root / 'Quillen.lean').read_text())
        self.assertEqual(root_imports, [])  # Native mk_all owns this entry.

    def test_exact_marker_regenerates_owned_future_facade(self):
        directory = self.root / 'Quillen/Future'
        directory.mkdir()
        (directory / 'Leaf.lean').write_text('')
        facade = self.root / 'Quillen/Future.lean'
        facade.write_text(GENERATED_MARKER + 'import Quillen.Future.Removed\n')
        self.assertIn(Path('Quillen/Future.lean'), stale_files(self.root))
        self.generate()
        self.assertEqual(project_imports(facade.read_text()), ['Quillen.Future.Leaf'])

    def test_owned_marker_after_copyright_and_manual_mention_are_distinct(self):
        facade = self.root / 'Quillen/Algebra.lean'
        facade.write_text(COPYRIGHT_HEADER + GENERATED_MARKER + 'import Quillen.Removed\n')
        self.assertIn(Path('Quillen/Algebra.lean'), generated_files(self.root))
        self.generate()
        self.assertTrue(facade.read_text().startswith(COPYRIGHT_HEADER + GENERATED_MARKER))
        manual = COPYRIGHT_HEADER + '/-! Manual module.\n' + GENERATED_MARKER + '-/\n'
        facade.write_text(manual)
        self.generate()
        self.assertEqual(facade.read_text(), manual)

    def test_nested_generation_requires_existing_opt_in_and_preserves_manual_api(self):
        nested = self.root / 'Quillen/Algebra/Nested'
        nested.mkdir()
        (nested / 'Leaf.lean').write_text('')
        owned = nested.with_suffix('.lean')
        owned.write_text(COPYRIGHT_HEADER + GENERATED_MARKER + 'import Quillen.Removed\n')
        manual_dir = self.root / 'Quillen/Algebra/Selected'
        manual_dir.mkdir()
        (manual_dir / 'Leaf.lean').write_text('')
        manual = manual_dir.with_suffix('.lean')
        original = COPYRIGHT_HEADER + 'import Quillen.Algebra.Selected.Leaf\n'
        manual.write_text(original)
        hidden = self.root / 'Quillen/Algebra/NoFacade'
        hidden.mkdir()
        (hidden / 'Leaf.lean').write_text('')
        self.generate()
        self.assertEqual(project_imports(owned.read_text()), ['Quillen.Algebra.Nested.Leaf'])
        self.assertEqual(manual.read_text(), original)
        self.assertFalse(hidden.with_suffix('.lean').exists())
        self.assertEqual(stale_files(self.root), [])
        (nested / 'New.lean').write_text('')
        self.assertIn(Path('Quillen/Algebra/Nested.lean'), stale_files(self.root))

    def test_modern_thematic_generation_keeps_native_and_test_entries_untouched(self):
        for path in (self.root / 'Quillen').rglob('*.lean'):
            path.write_text('module\n')
        (self.root / 'Quillen.lean').write_text('module\n')
        tests = self.root / 'QuillenTest'
        tests.mkdir()
        (tests / 'Positive.lean').write_text('import Quillen\n')
        for path, content in generated_files(self.root, modern_library=True).items():
            (self.root / path).write_text(content)
        self.assertEqual(stale_files(self.root), [])
        self.assertIn('module\n\npublic import Quillen.Algebra.A',
                      (self.root / 'Quillen/Algebra.lean').read_text())
        self.assertEqual((self.root / 'Quillen.lean').read_text(), 'module\n')
        self.assertFalse((self.root / 'QuillenTest.lean').exists())
        (self.root / 'Quillen/Algebra/A.lean').write_text('def old : Nat := 1\n')
        with self.assertRaisesRegex(ValueError, 'cannot import legacy sources'):
            generated_files(self.root)

if __name__ == '__main__':
    unittest.main()
