#!/usr/bin/env python3
"""Behavioral regression tests for library boundaries and enrollment."""
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

from lean_ci.quillen.check_library_layout import check_layout, import_cycles
from lean_ci.quillen.generate_imports import generated_files, stale_files
from lean_ci.quillen.library_sources import lean_imports, uses_module_system



class LayoutGuardTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-layout-')
        self.root = Path(self.tmp.name)
        self.write('Quillen/Algebra/A.lean', 'import Mathlib.Data.Nat.Basic\n')
        self.write('Quillen/Algebra/B.lean', 'import Quillen.Algebra.A\n')
        self.write('Quillen/Library.lean', 'import Quillen.Algebra.B\n')
        self.generate()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def generate(self):
        for path, content in generated_files(self.root).items():
            self.write(path, content)
        # Fixture input supplied as native mk_all would; the Python generator
        # under test owns only thematic/client facades.
        names = sorted('.'.join(path.relative_to(self.root).with_suffix('').parts)
                       for path in (self.root / 'Quillen').rglob('*.lean'))
        self.write('Quillen.lean', ''.join('import ' + name + '\n' for name in names))

    def rejected(self, phrase):
        errors, _ = check_layout(self.root)
        self.assertTrue(any(phrase in error for error in errors), '\n'.join(errors))

    def test_missing_enrollment_even_for_orphan_module(self):
        self.write('Quillen/Algebra/Orphan.lean', '')
        self.rejected('missing enrollment')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])

    def test_native_root_enrollment_is_left_to_mk_all(self):
        self.write('Quillen.lean', 'import Quillen.Library\n')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_library_test_import_bypasses_are_rejected(self):
        for imported in ('Consumer.Bad', 'Tests.Bad', '«Tests».Bad', 'Quillen.Tests.Bad',
                         'QuillenTest.Bad', '«QuillenTest».Bad', 'audits.Bad',
                         'Quillen.QuillenTest.Bad', '«Consumer».Bad'):
            with self.subTest(imported=imported):
                self.write('Quillen/Algebra/A.lean',
                           'public meta import Mathlib.Foo /- hidden delimiter -/\nimport '
                           + imported + '\n')
                self.rejected('Forbidden library import')

    def test_modern_import_all_keeps_boundary_and_resolution_guards(self):
        self.write('Quillen/Algebra/A.lean', 'module\npublic meta import all QuillenTest.Bad\n')
        self.rejected('Forbidden library import')
        self.write('Quillen/Algebra/A.lean', 'module\nimport all Quillen.Missing\n')
        self.rejected('Unresolved local import')

    def test_library_cannot_depend_on_workspace_tooling(self):
        for imported in ('Tools.Helper', '«Tools».Helper', 'scripts.Helper'):
            with self.subTest(imported=imported):
                self.write('Quillen/Algebra/A.lean', 'module\npublic meta import ' + imported + '\n')
                self.rejected('Forbidden library import')
        self.write('Quillen/Algebra/A.lean', 'import Mathlib.Tools.Helper\n')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_fake_imports_in_comments_and_strings_do_not_create_failures(self):
        self.write('Quillen/Algebra/A.lean', '''/- import Consumer.Bad /- nested -/ -/
def s := "import QuillenTest.Bad"
''')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_unresolved_import_in_library_and_consumer(self):
        self.write('Quillen/Algebra/A.lean', 'import Quillen.NoSuchModule\n')
        self.rejected('Unresolved local import')
        self.write('Quillen/Algebra/A.lean', '')
        self.write('examples/downstream/Consumer.lean', 'import Consumer.Bad\n')
        self.write('examples/downstream/Consumer/Bad.lean', 'import Quillen.NoSuchModule\n')
        self.generate()
        self.rejected('Unresolved local import')

    def test_direct_indirect_and_self_cycles(self):
        for a, b in (('Quillen.Algebra.B', 'Quillen.Algebra.A'),
                     ('Quillen.Algebra.A', 'Quillen.Algebra.A')):
            with self.subTest(a=a, b=b):
                self.write('Quillen/Algebra/A.lean', 'import ' + a + '\n')
                self.write('Quillen/Algebra/B.lean', 'import ' + b + '\n')
                self.rejected('Project import cycle')

    def test_implementation_broad_facade_import_rejected(self):
        self.write('Quillen/Algebra/A.lean', 'import Quillen.Library\n')
        self.rejected('Implementation imports broad facade')

    def test_nested_manual_and_generated_topic_facades_are_broad_surfaces(self):
        self.write('Quillen/Algebra/API/Leaf.lean', '')
        self.write('Quillen/Algebra/API.lean', 'import Quillen.Algebra.API.Leaf\n')
        self.write('Quillen/Algebra/Generated/Leaf.lean', '')
        from lean_ci.quillen.generate_imports import COPYRIGHT_HEADER, GENERATED_MARKER
        self.write('Quillen/Algebra/Generated.lean', COPYRIGHT_HEADER + GENERATED_MARKER)
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])
        for surface in ('Quillen.Algebra.API', 'Quillen.Algebra.Generated'):
            with self.subTest(surface=surface):
                self.write('Quillen/Algebra/A.lean', 'import ' + surface + '\n')
                self.rejected('Implementation imports broad facade')
        self.write('Quillen/Algebra/A.lean', '')
        self.write('Quillen/Algebra/API.lean', 'import Quillen.Algebra.Generated\n')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_orphan_generator_marker_requires_a_corresponding_directory(self):
        from lean_ci.quillen.generate_imports import COPYRIGHT_HEADER, GENERATED_MARKER
        self.write('Quillen/Algebra/Orphan.lean', COPYRIGHT_HEADER + GENERATED_MARKER)
        self.generate()
        self.rejected('no corresponding directory')

    def test_foundation_with_extension_directory_is_not_a_broad_facade(self):
        self.write('Quillen/Algebra/Foundation.lean', 'def foundation : Nat := 1\n')
        self.write('Quillen/Algebra/Foundation/Extension.lean',
                   'import Quillen.Algebra.Foundation\n')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])
        self.write('Quillen/Algebra/Foundation.lean',
                   'module\npublic import Quillen.Algebra.B\n'
                   '/-! Manual API. -/\n@[expose] public section\n')
        self.rejected('Implementation imports broad facade')

    def test_extra_family_and_facade_supported(self):
        self.write('Quillen/Future/X.lean', '')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])

    def test_loose_root_source_rejected(self):
        self.write('StrayAudit.lean', 'import Quillen\n')
        self.rejected('Unclassified project-root Lean files')

    def test_deep_acyclic_graph_does_not_hit_recursion_limit(self):
        graph = {f'M{i}': {f'M{i+1}'} for i in range(2000)}
        self.assertEqual(import_cycles(graph), [])
        graph['M2000'] = {'M0'}
        self.assertTrue(import_cycles(graph))


    def test_trust_tests_accept_production_imports_and_require_enrollment(self):
        self.write('QuillenTest/Axioms.lean', 'import Quillen\n')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])
        self.write('QuillenTest/NewPositiveTest.lean', 'import Quillen.Algebra.A\n')
        self.assertEqual(check_layout(self.root)[0], [])  # Test globs enroll it.
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])

    def test_core_cannot_import_test_root_or_test_leaf(self):
        self.write('QuillenTest/Check.lean', 'import Quillen.Algebra.A\n')
        self.generate()
        for imported in ('QuillenTest', 'QuillenTest.Check'):
            with self.subTest(imported=imported):
                self.write('Quillen/Algebra/B.lean', 'import ' + imported + '\n')
                self.rejected('Forbidden library import')

    def test_trust_test_cycle_is_detected(self):
        self.write('QuillenTest/A.lean', 'import QuillenTest.B\n')
        self.write('QuillenTest/B.lean', 'import QuillenTest.A\n')
        self.generate()
        self.rejected('Project import cycle')

    def test_unresolved_test_import_is_detected(self):
        self.write('QuillenTest/A.lean', 'import QuillenTest.Missing\n')
        self.generate()
        self.rejected('Unresolved local import')

    def test_downstream_imports_resolve_in_independent_package(self):
        self.write('examples/downstream/Consumer.lean', 'import Consumer.RealClient\n')
        self.write('examples/downstream/Consumer/RealClient.lean', 'import Quillen.Library\n')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])
        self.write('examples/downstream/Consumer/RealClient.lean', 'import Consumer.Missing\n')
        self.rejected('Unresolved local import')

    def test_modern_consumer_rejects_legacy_child_before_build(self):
        self.write('examples/downstream/Consumer.lean',
                   'module\npublic import Consumer.Existing\n')
        self.write('examples/downstream/Consumer/Existing.lean', 'module\n')
        self.generate()
        # Even a previously unlisted child must not escape the module guard.
        self.write('examples/downstream/Consumer/NewClient.lean', 'import Quillen.Library\n')
        for check in (generated_files, stale_files, check_layout):
            with self.subTest(check=check.__name__):
                with self.assertRaisesRegex(ValueError,
                                            'Modern Consumer.*Consumer/NewClient.lean'):
                    check(self.root)
        original = (self.root / 'examples/downstream/Consumer.lean').read_bytes()
        for arguments in ([], ['--check']):
            result = subprocess.run(
                [sys.executable, '-m', 'lean_ci', 'quillen', 'imports',
                 '--root', str(self.root), *arguments], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Consumer/NewClient.lean', result.stderr)
            self.assertEqual((self.root / 'examples/downstream/Consumer.lean').read_bytes(),
                             original)
        self.assertTrue(uses_module_system(original.decode()))

    def test_consumer_enrollment_tracks_added_removed_and_nested_clients(self):
        facade = Path('examples/downstream/Consumer.lean')
        self.write(str(facade), 'module\n')
        self.write('examples/downstream/Consumer/Existing.lean', 'module\n')
        self.generate()
        self.write('examples/downstream/Consumer/New/Nested.lean', 'module\n')
        # A mathematical example's filename is not an audit-implementation flag.
        self.write('examples/downstream/Consumer/Audit.lean', 'module\npublic import Quillen.Library\n')
        self.write('examples/downstream/.lake/Consumer/Cached.lean', '')
        self.rejected('missing enrollment')
        self.generate()
        self.assertEqual(lean_imports((self.root / facade).read_text()),
                         ['Consumer.Audit', 'Consumer.Existing', 'Consumer.New.Nested'])
        self.assertEqual(check_layout(self.root)[0], [])
        (self.root / 'examples/downstream/Consumer/Existing.lean').unlink()
        self.rejected('missing enrollment')
        self.generate()
        self.assertEqual(lean_imports((self.root / facade).read_text()),
                         ['Consumer.Audit', 'Consumer.New.Nested'])
        self.assertEqual(check_layout(self.root)[0], [])

    def test_manual_future_facade_and_leaf_both_enrolled(self):
        self.write('Quillen/Future/A.lean', '')
        self.write('Quillen/Future.lean', 'import Quillen.Future.A\n\ndef answer : Nat := 42\n')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])


if __name__ == '__main__':
    unittest.main()
