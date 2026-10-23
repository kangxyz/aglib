# Authors: kangxyz
"""Fixed behavioral regressions for portable source discovery and policy guards."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check_library_layout import check_layout, import_cycles, forbidden_domain_import
from check_placeholders import check_placeholders
from check_source_policy import check_source_policy
from library_sources import lean_imports, module_path, test_modules as positive_modules
from library_sources import (is_import_surface, uses_module_system, generate_topic,
                             GENERATED_MARKER, LEGACY_GENERATED_MARKER)

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
        # Source-only fixtures supply ordinary import facades; mk_all owns real entries.
        for directory in sorted((self.root / 'Aglib').iterdir()):
            if directory.is_dir():
                names = sorted('.'.join(p.relative_to(self.root).with_suffix('').parts)
                               for p in directory.rglob('*.lean'))
                self.write('Aglib/' + directory.name + '.lean',
                           'module\n' + ''.join('public import ' + n + '\n' for n in names))
        names = sorted('.'.join(p.relative_to(self.root).with_suffix('').parts)
                       for p in (self.root / 'Aglib').rglob('*.lean'))
        self.write('Aglib.lean', 'module\n' + ''.join('public import ' + n + '\n' for n in names))

    def rejected(self, expected):
        errors, _ = check_layout(self.root)
        self.assertTrue(any(expected in error for error in errors), errors)

    def test_clean_modern_tree(self):
        self.assertEqual(check_layout(self.root)[0], [])
        self.assertEqual(check_placeholders(self.root), [])
        self.assertEqual(check_source_policy(self.root), [])



    def test_native_test_discovery_needs_no_umbrella(self):
        self.write('AglibTest/Positive.lean', HEADER)
        self.assertEqual(positive_modules(self.root), {Path('AglibTest/Positive.lean')})
        self.assertFalse((self.root / 'AglibTest.lean').exists())
        self.write('AglibTest.lean', 'import AglibTest.Positive\n')
        self.assertEqual(positive_modules(self.root),
                         {Path('AglibTest/Positive.lean'), Path('AglibTest.lean')})

    def test_removed_audit_fixture_directory_has_no_placeholder_exemption(self):
        self.write('AglibTest/NegativeControls/Bad.lean', 'axiom bad : False\n')
        errors = check_placeholders(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn('forbidden token axiom', errors[0])

    def test_copyright_headers_require_and_preserve_author_credit(self):
        header = ('/-\nCopyright (c) 2026 Test contributors. All rights reserved.\n'
                  'Released under Apache 2.0 license as described in the file LICENSE.\n')
        for credit in ['', 'Authors: \n']:
            self.write('Aglib/Algebra/A.lean', header + credit + '-/\n' + HEADER)
            self.assertTrue(any('Authors credit' in error
                                for error in check_source_policy(self.root)))
        source = header + 'Authors: Upstream contributor\n-/\n' + HEADER
        self.write('Aglib/Algebra/A.lean', source)
        self.assertEqual(check_source_policy(self.root), [])
        self.assertEqual((self.root / 'Aglib/Algebra/A.lean').read_text(), source)

    def test_extraction_notice_is_not_replaced_with_a_copyright_header(self):
        source = ('/-\nExtracted source; no upstream license is declared.\n'
                  'Original attribution is retained below.\n-/\n' + HEADER)
        self.write('Aglib/Algebra/A.lean', source)
        self.assertEqual(check_source_policy(self.root), [])
        self.assertEqual((self.root / 'Aglib/Algebra/A.lean').read_text(), source)

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
        for name in ['KTheory', 'GTheory', 'QConstruction', 'SConstruction', 'Plus', 'Bass',
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


    def test_placeholders_scan_all_positive_sources_and_clients(self):
        self.write('Aglib/Algebra/A.lean', HEADER + 'example : True := by sorry\n')
        self.write('AglibTest/Positive.lean', 'example : True := by admit\n')
        self.write('AglibTest/Extra.lean', 'axiom bad : False\n')
        self.write('examples/downstream/Consumer/Bad.lean', 'axiom bad : False\n')
        self.write('examples/downstream/.lake/packages/Foreign/Bad.lean', 'sorry\n')
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

    def test_constant_identifier_is_not_a_source_assumption(self):
        self.write('Aglib/Algebra/A.lean', HEADER + '''
namespace Field.DivisorData
abbrev constant (d : Data) (a : C) : K := d.constants a
theorem constant_one : d.constant 1 = 1 := d.map_one
def useConstant := Field.DivisorData.constant d a
def «constant» : Nat := 1
def «unsafe def» : Nat := 2
def text := "constant bad : False; unsafe opaque bad : Nat"
/- constant bad : False /- unsafe def bad := 0 -/ -/
end Field.DivisorData
''')
        self.assertEqual(check_source_policy(self.root), [])

    def test_actual_constant_and_unsafe_commands_remain_rejected(self):
        for source in [
                'constant bad : False\n',
                'public constant /- name -/ «quoted name» : False\n',
                'namespace N\nprivate constant bad : False\nend N\n',
                'constant constant : False\n',
                'unsafe def bad : Nat := 0\n',
                'private unsafe /- nested /- comment -/ -/ opaque «constant» : Nat := 0\n',
                'noncomputable unsafe\ndef bad : Nat := 0\n']:
            with self.subTest(source=source):
                self.write('Aglib/Algebra/A.lean', HEADER + source)
                errors = check_source_policy(self.root)
                self.assertEqual(len(errors), 1, errors)
                self.assertIn('unsupported source assumption or unsafe implementation', errors[0])

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

    def test_reusable_curve_and_surface_geometry_is_admitted(self):
        for name in ['Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle',
                     'Aglib.AlgebraicGeometry.Curves.Picard.Degree',
                     'Aglib.AlgebraicGeometry.Curves.Genus',
                     'Aglib.AlgebraicGeometry.ProjectiveLine.Charts',
                     'Aglib.AlgebraicGeometry.Divisors.Relative.Basic',
                     'Aglib.AlgebraicGeometry.Stalk.FlatDVR.Component']:
            with self.subTest(name=name):
                self.assertFalse(forbidden_domain_import(name))
        for name in ['R5Lab.AlgebraicGeometry.Curves.Basic',
                     'Quillen.AlgebraicGeometry.Curves.Basic',
                     'Aglib.AlgebraicGeometry.Curves.KTheory.Basic',
                     'Aglib.AlgebraicGeometry.Curves.SConstruction.Basic']:
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
                with self.assertRaisesRegex(ValueError, 'manually owned or non-import-only'):
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
        with self.assertRaisesRegex(ValueError, 'consumer of that same entry'):
            generate_topic(self.root, 'Aglib.NewFamily')
        self.assertFalse(self.facade.exists())

    def test_actual_cli_generates_only_when_explicitly_requested(self):
        script = Path(__file__).resolve().parents[1] / 'check_library_layout.py'
        result = subprocess.run([sys.executable, '-B', str(script), '--root', str(self.root),
                                 '--generate', 'Aglib.NewFamily'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('longFile = 0', result.stdout)
        self.assertTrue(self.facade.is_file())


if __name__ == '__main__':
    unittest.main()
