"""Fixed behavioral regressions for portable source discovery and policy guards."""
from pathlib import Path
import tempfile
import unittest

from check_library_layout import check_layout, import_cycles, forbidden_domain_import
from check_placeholders import check_placeholders
from check_source_policy import check_source_policy
from generate_imports import GENERATED_MARKER, generated_files, generator_owned, stale_files
from library_sources import lean_imports, module_path, test_modules as positive_modules

HEADER = 'module\npublic import Mathlib.Data.Nat.Basic\n@[expose] public section\n'


class SourceGuards(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='ag-source-guards-')
        self.root = Path(self.tmp.name)
        self.write('Aglib/Algebra/A.lean', HEADER + 'def value : Nat := 1\n')
        self.write('Aglib/Algebra/B.lean',
                   'module\npublic import Aglib.Algebra.A\n'
                   '@[expose] public section\ndef next : Nat := value + 1\n')
        self.generate()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, source):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)

    def generate(self):
        for path, source in generated_files(self.root).items():
            self.write(path, source)

    def rejected(self, expected):
        errors, _ = check_layout(self.root)
        self.assertTrue(any(expected in error for error in errors), errors)

    def test_clean_modern_tree(self):
        self.assertEqual(check_layout(self.root)[0], [])
        self.assertEqual(check_placeholders(self.root), [])
        self.assertEqual(check_source_policy(self.root), [])

    def test_parser_nested_comments_strings_quoted_roots_import_all(self):
        text = '''/- import R5Lab.Fake /- nested -/ -/
module
public meta import /- between -/ all «Aglib».Algebra.A
  Aglib.Algebra.B
private import Mathlib.Data.Nat.Basic
#check "import Quillen.Fake"
'''
        self.assertEqual(lean_imports(text), ['Aglib.Algebra.A',
                         'Aglib.Algebra.B', 'Mathlib.Data.Nat.Basic'])
        self.assertEqual(module_path('Aglib.«A.B»'),
                         Path('Aglib/A.B.lean'))

    def test_root_enrolls_even_orphan_leaves(self):
        self.write('Aglib/New/Orphan.lean', HEADER + 'def orphan : Nat := 2\n')
        self.rejected('missing enrollment')
        self.generate()
        self.assertEqual(stale_files(self.root), [])
        self.assertEqual(check_layout(self.root)[0], [])

    def test_empty_directories_do_not_create_placeholders(self):
        (self.root / 'Aglib/Empty').mkdir()
        self.assertNotIn(Path('Aglib/Empty.lean'), generated_files(self.root))

    def test_hand_owned_family_is_preserved_and_enrolled(self):
        source = 'module\npublic import Aglib.Algebra.A\n'
        self.write('Aglib/Algebra.lean', source)
        self.generate()
        self.assertEqual((self.root / 'Aglib/Algebra.lean').read_text(), source)
        self.assertIn('Aglib.Algebra', lean_imports(
            (self.root / 'Aglib.lean').read_text()))

    def test_nested_owned_facades_receive_new_leaves(self):
        self.write('Aglib/Algebra/Nested/Leaf.lean', HEADER)
        self.write('Aglib/Algebra/Nested.lean', GENERATED_MARKER)
        self.generate()
        self.assertIn('Aglib.Algebra.Nested.Leaf', lean_imports(
            (self.root / 'Aglib/Algebra/Nested.lean').read_text()))
        self.assertEqual(check_layout(self.root)[0], [])

    def test_marker_inside_prose_does_not_transfer_ownership(self):
        self.assertFalse(generator_owned('/-! ' + GENERATED_MARKER + '-/\n'))
        self.assertFalse(generator_owned('module\n' + GENERATED_MARKER))
        self.assertTrue(generator_owned(GENERATED_MARKER))

    def test_removed_leaf_stales_generation(self):
        (self.root / 'Aglib/Algebra/B.lean').unlink()
        self.assertTrue(stale_files(self.root))

    def test_positive_root_excludes_audits_and_negative_controls(self):
        self.write('AglibTest/Positive.lean',
                   'module\npublic import Aglib.Algebra.A\n')
        for path in ['Axioms.lean', 'AuditSupport.lean', 'NegativeControls/Bad.lean']:
            self.write('AglibTest/' + path, 'import Lean\n')
        self.generate()
        imports = lean_imports((self.root / 'AglibTest.lean').read_text())
        self.assertEqual(imports, ['AglibTest.Positive'])
        self.assertEqual(len(positive_modules(self.root)), 2)
        self.assertEqual(check_layout(self.root)[0], [])

    def test_positive_cannot_import_negative_control(self):
        self.write('AglibTest/NegativeControls/Bad.lean', 'import Lean\n')
        self.write('AglibTest/Positive.lean',
                   'import AglibTest.NegativeControls.Bad\n')
        self.generate()
        self.rejected('Positive fixture imports audit')

    def test_production_only_mathlib_and_foundation(self):
        for name in ['AGLib.Algebra.A', 'AGLibTest.Positive',
                     'R5Lab.RingTheory.A', '«Quillen».Exact', 'Essays.Note',
                     'Tests.Bad', 'Tools.Script', 'AglibTest.Positive',
                     'Lean.Util.CollectAxioms', 'Batteries.Tactic']:
            with self.subTest(name=name):
                self.write('Aglib/Algebra/A.lean',
                           'module\npublic import ' + name + '\n@[expose] public section\n')
                self.rejected('Forbidden')

    def test_prohibited_application_families(self):
        for name in ['Curves', 'P1', 'Genus', 'Degree', 'RiemannRoch', 'KTheory',
                     'GTheory', 'QConstruction', 'SConstruction', 'Plus', 'Bass',
                     'Spectra']:
            with self.subTest(name=name):
                self.write('Aglib/Algebra/A.lean',
                    'module\npublic import Aglib.' + name + '.Bad\n')
                self.rejected('Forbidden domain import')

    def test_exposed_public_noncomputable_section_is_an_implementation(self):
        self.write('Aglib/Algebra/A.lean', HEADER.replace(
            '@[expose] public section', '@[expose] public noncomputable section') +
            'def datum : Nat := 1\n')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_general_milnor_owner_keeps_other_k_applications_out(self):
        for name in ['Aglib.KTheory', 'Aglib.KTheory.MilnorK',
                     'Aglib.KTheory.MilnorK.K2.Basic',
                     'Aglib.KTheory.MilnorK.Norm.FiniteExtension.Tower']:
            self.assertFalse(forbidden_domain_import(name))
        for name in ['Aglib.KTheory.Quillen.Basic',
                     'Aglib.KTheory.MilnorK.SConstruction.Basic',
                     'Aglib.Other.KTheory.MilnorK.Basic']:
            self.assertTrue(forbidden_domain_import(name))

    def test_retained_namespaces_and_comments_are_allowed(self):
        self.write('Aglib/Algebra/A.lean', HEADER +
            '/- Quillen.KTheory and R5Lab.Curves are source provenance. -/\n'
            'namespace Quillen.Devissage\ndef result : Nat := 1\nend Quillen.Devissage\n')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_unresolved_import_and_cycles(self):
        self.write('Aglib/Algebra/A.lean',
                   'module\npublic import Aglib.Missing\n')
        self.rejected('Unresolved local import')
        self.write('Aglib/Algebra/A.lean',
                   'module\npublic import Aglib.Algebra.B\n')
        self.rejected('Project import cycle')
        self.assertEqual(import_cycles({f'M{i}': {f'M{i+1}'} for i in range(2000)}), [])

    def test_precise_implementation_imports_no_facades(self):
        self.write('Aglib/Algebra/A.lean',
                   'module\npublic import Aglib.Algebra\n'
                   '@[expose] public section\ndef value : Nat := 1\n')
        self.rejected('Implementation imports broad facade')

    def test_modern_public_exports_are_required(self):
        self.write('Aglib/Algebra/A.lean', 'import Mathlib.Data.Nat.Basic\n')
        self.rejected('lacks modern module header')
        self.write('Aglib/Algebra/A.lean', 'module\nimport Mathlib.Data.Nat.Basic\n')
        self.rejected('lacks public modifier')
        self.write('Aglib/Algebra/A.lean', 'module\ndef datum : Nat := 0\n')
        self.rejected('lacks exposed public section')

    def test_legacy_auditor_is_required(self):
        self.write('AglibTest/Axioms.lean', 'module\npublic import Aglib\n')
        self.rejected('must retain legacy private imports')

    def test_placeholders_scan_positives_clients_and_auditors(self):
        self.write('Aglib/Algebra/A.lean', HEADER + 'example : True := by sorry\n')
        self.write('AglibTest/Positive.lean', 'example : True := by admit\n')
        self.write('AglibTest/Axioms.lean', 'axiom bad : False\n')
        self.write('examples/downstream/Consumer/Bad.lean', 'axiom bad : False\n')
        self.write('examples/downstream/.lake/packages/Foreign/Bad.lean', 'sorry\n')
        self.write('AglibTest/NegativeControls/Bad.lean', 'axiom bad : False\n')
        self.generate()
        errors = check_placeholders(self.root)
        self.assertEqual(len(errors), 4, errors)

    def test_placeholder_comments_strings_ignored(self):
        self.write('Aglib/Algebra/A.lean', HEADER +
                   '/- sorry /- axiom -/ admit -/\ndef text := "sorry axiom admit"\n')
        self.assertEqual(check_placeholders(self.root), [])

    def test_independent_client_resolution(self):
        self.write('examples/downstream/Consumer.lean', 'import Consumer.Client\n')
        self.write('examples/downstream/Consumer/Client.lean', 'import Aglib.Algebra.A\n')
        self.assertEqual(check_layout(self.root)[0], [])
        self.write('examples/downstream/Consumer/Client.lean', 'import Consumer.Missing\n')
        self.rejected('Unresolved local import')

    def test_global_heartbeat_and_unexplained_modifications_are_rejected(self):
        for option in ['maxHeartbeats', 'synthInstance.maxHeartbeats']:
            for source in [f'set_option {option} 400000\ndef datum := 1\n',
                           f'set_option {option} 0\ndef datum := 1\n',
                           f'set_option {option} 400000 in\ndef datum := 1\n',
                           f'set_option {option} 0 in\ndef datum := 1\n',
                           f'-- Before the option only.\nset_option {option} 200000 in\n'
                           'def datum := 1\n']:
                with self.subTest(option=option, source=source):
                    self.write('Aglib/Algebra/A.lean', HEADER + source)
                    self.assertTrue(check_source_policy(self.root))

    def test_other_fixed_source_safety_is_preserved(self):
        for source in ['set_option autoImplicit true\n',
                       'set_option warningAsError false\n',
                       'set_option linter.mathlibStandardSet false\n']:
            with self.subTest(source=source):
                self.write('Aglib/Algebra/A.lean', HEADER + source)
                self.assertTrue(check_source_policy(self.root))

    def test_documented_local_positive_heartbeat_budgets(self):
        for option in ['maxHeartbeats', 'synthInstance.maxHeartbeats',
                       '«synthInstance».«maxHeartbeats»',
                       'foo.maxHeartbeats.bar', '«with spaces».maxHeartbeats']:
            for value in ['1', '200000', '400000', '200_000', '0x10', '0X0_1',
                          '0b1', '0B0_1', '0o1', '0O0_1']:
                for comment in ['-- Explanation supplied by the mathematical owner.\n',
                                '/- Explanation supplied by the mathematical owner. -/\n']:
                    with self.subTest(option=option, value=value, comment=comment):
                        self.write('Aglib/Algebra/A.lean', HEADER +
                            f'set_option {option} {value} in\n' + comment + 'def datum := 1\n')
                        self.assertEqual(check_source_policy(self.root), [])

    def test_documented_local_zero_heartbeat_budgets_are_rejected(self):
        for option in ['maxHeartbeats', 'synthInstance.maxHeartbeats',
                       '«synthInstance».«maxHeartbeats»',
                       'foo.maxHeartbeats.bar', '«with spaces».maxHeartbeats']:
            for value in ['0', '00', '0000', '0_0', '0__0', '0x0', '0x00',
                          '0X0_0', '0b0', '0B0_0', '0o00', '0O0_0']:
                for comment in ['-- A local explanation cannot allow unlimited work.\n',
                                '/- A local explanation cannot allow unlimited work. -/\n']:
                    with self.subTest(option=option, value=value, comment=comment):
                        self.write('Aglib/Algebra/A.lean', HEADER +
                            f'set_option {option} {value} in\n' + comment + 'def datum := 1\n')
                        errors = check_source_policy(self.root)
                        self.assertEqual(len(errors), 1, errors)
                        self.assertIn('positive and finite', errors[0])

    def test_heartbeat_lexical_boundaries(self):
        self.write('Aglib/Algebra/A.lean', HEADER + '''
/- set_option maxHeartbeats 0 in /- nested -/ -/
-- set_option synthInstance.maxHeartbeats 0
def text := "set_option maxHeartbeats 0 in \\"quoted\\""
def «set_option maxHeartbeats 0» := 1
set_option «foo maxHeartbeats».«bar--baz» 0
def datum := 1
''')
        self.assertEqual(check_source_policy(self.root), [])
        self.write('Aglib/Algebra/A.lean', HEADER + '''
set_option /- option -/ «with /- spaces -/».«maxHeartbeats» /- budget -/ 0x00 in
/- Explanation /- nested -/ supplied. -/
def datum := 1
''')
        errors = check_source_policy(self.root)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn(':5: heartbeat budgets must be positive and finite', errors[0])

    def test_heartbeat_option_next_to_term_punctuation(self):
        for value in ['0', '400000']:
            with self.subTest(value=value):
                self.write('Aglib/Algebra/A.lean', HEADER +
                           f'def datum : Nat := (set_option maxHeartbeats {value} in\n'
                           '-- Explanation for this term.\n1)\n')
                errors = check_source_policy(self.root)
                if value == '0':
                    self.assertTrue(any('positive and finite' in error for error in errors), errors)
                else:
                    self.assertEqual(errors, [])

    def test_scope_requires_the_in_keyword(self):
        self.write('Aglib/Algebra/A.lean', HEADER +
                   "set_option maxHeartbeats 400000 in'\n"
                   '-- This is not the scope keyword.\ndef datum := 1\n')
        errors = check_source_policy(self.root)
        self.assertTrue(any('declaration-local' in error for error in errors), errors)

    def test_heartbeat_rule_matches_name_components_not_substrings(self):
        for option in ['maxHeartbeatsExtra', '«foo.maxHeartbeats»', 'maxRecDepth']:
            with self.subTest(option=option):
                self.write('Aglib/Algebra/A.lean', HEADER + f'set_option {option} 0\n')
                self.assertEqual(check_source_policy(self.root), [])

    def test_canonical_degree_leaves_are_not_degree_applications(self):
        prefix = 'Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel'
        for owner in ['Class', 'Insertion']:
            with self.subTest(owner=owner):
                self.assertFalse(forbidden_domain_import(f'{prefix}.{owner}.Degree'))
                self.assertTrue(forbidden_domain_import(f'{prefix}.{owner}.Degree.Curves'))
                self.assertTrue(forbidden_domain_import(f'{prefix}.{owner}.Degree.Future'))
        for name in [f'{prefix}.Other.Degree', 'Aglib.AlgebraicGeometry.Curves.Degree',
                     'Aglib.Other.Degree', 'Aglib.Degree.Basic']:
            with self.subTest(name=name):
                self.assertTrue(forbidden_domain_import(name))

    def test_bounded_below_plus_marker_is_distinct_from_application_plus(self):
        for name in ['Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle',
                     'Aglib.Algebra.Homology.HomotopyCategory.Plus.BoundedComparison',
                     'Aglib.AlgebraicGeometry.Cohomology.Cech.Resolution.Plus']:
            self.assertFalse(forbidden_domain_import(name))
        for name in ['Aglib.Plus.Basic', 'Aglib.PlusConstruction.Basic',
                     'Aglib.Other.DerivedCategory.Plus.Basic',
                     'Aglib.Algebra.Homology.DerivedCategory.Plus.KTheory.Application',
                     'Aglib.AlgebraicGeometry.Cohomology.Cech.Resolution.Plus.KTheory.Bad',
                     'Aglib.Other.Cech.Resolution.Plus']:
            self.assertTrue(forbidden_domain_import(name))


if __name__ == '__main__':
    unittest.main()
