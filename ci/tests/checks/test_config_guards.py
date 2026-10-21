"""Behavior tests for declarative source policy without invoking Lean."""
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.checks.guards import (check_budget, check_source, generated_files,
    check_links, markdown_link_targets, run)


class GuardsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.config = {'package_dir': '.', 'policy': {}, 'expected_failure': [], 'extra_sources': [],
                       'modules': {}, 'workspaces': [{'id': 'root', 'path': '.'}]}
        (self.root / 'lakefile.toml').write_text('[leanOptions]\nmaxHeartbeats = 200000\n')

    def source(self, name, source, role='production', workspace='root'):
        path = name.replace('.', '/') + '.lean'
        (self.root / path).parent.mkdir(parents=True, exist_ok=True)
        (self.root / path).write_text(source)
        key = name if workspace == 'root' else workspace + ':' + name
        self.config['modules'][key] = dict(module=name, path=path, role=role, workspace=workspace)
        return key

    def policy(self, category, data):
        path = category + '.json'
        (self.root / path).write_text(json.dumps(data))
        self.config['policy'].setdefault(category, []).append(path)

    def test_selected_bytes_do_not_inspect_unrelated_placeholders(self):
        self.source('Lib.Bad', 'theorem unfinished : True := by sorry\n')
        good = self.source('Lib.Good', '-- sorry\ndef s := "sorry"\ndef «sorry» := 1\n')
        self.assertEqual(check_source(self.root, self.config, [good]), [])
        self.assertTrue(any('forbidden token sorry' in e for e in check_source(self.root, self.config, ['Lib.Bad'])))

    def test_enrollment_edges_cycles_and_positive_test_boundary(self):
        self.source('Lib.One', 'import Lib.Two\nimport Test.Bad\n')
        self.source('Lib.Two', 'import Lib.One\n')
        self.source('Test.Bad', 'def x := 1\n', role='tests')
        errors = check_source(self.root, self.config, [])
        self.assertTrue(any('forbidden tests import' in e for e in errors))
        self.assertTrue(any('cycle' in e for e in errors))
        self.source('Lib.Missing', 'public meta import all Lib.Absent\n')
        self.assertTrue(any('unresolved' in e for e in check_source(self.root, self.config, [])))

    def test_candidate_external_and_quoted_module_boundaries(self):
        key = self.source('Host.Candidate.Leaf', 'import Host.Outside\nimport External.Basic\n')
        self.source('Host.Outside', 'def x := 0\n')
        self.policy('style', {'schema': 1, 'kind': 'source', 'external_roots': ['External'],
                             'import_boundaries': [{'origin_prefix': 'Host.Candidate', 'local_prefix': 'Host', 'allowed_prefixes': ['Host.Candidate']}]})
        errors = check_source(self.root, self.config, [key])
        self.assertEqual(len(errors), 1)
        self.assertIn('candidate imports host', errors[0])

    def test_component_exception_exempts_only_its_actual_owner(self):
        key = self.source('Lib.One', 'import Domain.Special.Plus\n')
        self.policy('style', {'schema': 1, 'kind': 'source', 'forbidden_components': ['plus', 'k'],
            'component_exceptions': [{'component': 'plus', 'at': 2, 'prefixes': ['Domain.Special.Plus']}]})
        self.assertEqual(check_source(self.root, self.config, [key]), [])
        self.source('Lib.One', 'import Domain.Special.Plus.K\n')
        self.assertTrue(any('forbidden domain' in error for error in check_source(self.root, self.config, [key])))

    def test_quoted_option_cannot_weaken_compiler_policy(self):
        key = self.source('Lib.One', 'set_option «warningAsError» false\n')
        self.assertTrue(any('weakens required option' in error for error in check_source(self.root, self.config, [key])))

    def test_component_roots_do_not_limit_separate_forbidden_roots(self):
        key = self.source('Lib.One', 'import External.K\nimport Forbidden.K\n', 'tests')
        self.policy('style', {'schema': 1, 'kind': 'source', 'forbidden_components': ['k'],
            'component_roots': ['Domain'], 'forbidden_roots': ['Forbidden'], 'domain_roles': ['production', 'tests'], 'domain_clients': True})
        errors = check_source(self.root, self.config, [key])
        self.assertEqual(len(errors), 1)
        self.assertIn('Forbidden.K', errors[0])
        self.source('Lib.One', 'import Domain.K\n', 'tests')
        self.assertTrue(any('Domain.K' in error for error in check_source(self.root, self.config, [key])))

    def test_changed_markdown_links_resolve_local_paths_and_optional_titles(self):
        (self.root / 'docs').mkdir()
        (self.root / 'target file.md').write_text('target')
        (self.root / 'docs/change.md').write_text('[local](<../target%20file.md#section> "Title")\n[folder](../docs/)\n[missing](absent.md)\n')
        (self.root / 'docs/unrelated.md').write_text('[old](unrelated-missing.md)\n')
        errors = check_links(self.root, ['docs/change.md'])
        self.assertEqual(errors, ['Broken local Markdown link in docs/change.md: absent.md'])
        targets = markdown_link_targets(self.root, ['docs/change.md'])
        self.assertIn('docs/absent.md', targets)
        self.assertIn('docs/../target file.md', targets)
        self.assertNotIn('docs/unrelated-missing.md', targets)

    def test_markdown_links_ignore_urls_anchors_and_code_examples(self):
        text = ('[remote](https://example.test/missing) [anchor](#section) [email](mailto:a@example.test)\n'
                '[absolute](/outside) [app](plugin://example/missing)\n'
                '`[inline](missing-inline.md)`\n'
                '`` [long inline](missing-long.md) ` inner ``\n'
                '```markdown\n[example](missing-fence.md)\n```\n'
                '~~~\n[example](missing-tilde.md)\n~~~\n'
                '    [indented](missing-code.md)\n')
        (self.root / 'change.md').write_text(text)
        self.assertEqual(check_links(self.root, ['change.md', 'deleted.md']), [])
        self.assertEqual(markdown_link_targets(self.root, ['change.md']), [])

    def test_markdown_link_escape_is_rejected_without_reading_outside(self):
        (self.root / 'change.md').write_text('[escape](../outside.md)\n')
        with self.assertRaisesRegex(ValueError, 'escapes repository'):
            check_links(self.root, ['change.md'])
        (self.root / 'linked').symlink_to(self.root.parent, target_is_directory=True)
        (self.root / 'change.md').write_text('[symlink](linked/outside.md)\n')
        with self.assertRaisesRegex(ValueError, 'escapes repository'):
            markdown_link_targets(self.root, ['change.md'])

    def test_source_dispatch_checks_supplied_markdown(self):
        (self.root / 'change.md').write_text('[missing](missing.md)\n')
        with patch('lean_ci.checks.guards.check_source', return_value=[]) as source:
            self.assertEqual(run('source', self.root, [], config=self.config, repo_root=self.root, changed_paths=['change.md']), 1)
            source.assert_called_once()

    def test_generated_marker_and_inventory_addition(self):
        self.source('Lib.Topic', '-- Generated by scripts/generate_imports.py; do not edit by hand.\nmodule\npublic import Lib.Topic.One\n')
        self.source('Lib.Topic.One', 'module\n')
        self.source('Lib.Manual', 'import Lib.Topic.One\n')
        self.policy('style', {'schema': 1, 'kind': 'source', 'discover_generated': [{'root': 'Lib', 'marker': '-- Generated by scripts/generate_imports.py; do not edit by hand.'}]})
        self.assertEqual(check_source(self.root, self.config, []), [])
        self.source('Lib.Topic.Two', 'module\n')
        self.assertTrue(any('stale generated' in e for e in check_source(self.root, self.config, [])))

    def test_canonical_generated_credits_and_manual_ownership(self):
        leaf = self.source('Lib.Topic.One', '/-\nCopyright (c) 2026 Team.\nAuthors: Ada, Grace\n-/\nmodule\n')
        facade = self.source('Lib.Topic', '-- Generated by scripts/generate_imports.py; do not edit by hand.\nmodule\npublic import Lib.Topic.One\n')
        self.policy('style', {'schema': 1, 'kind': 'source', 'generated': [{
            'module': facade, 'mode': 'descendants', 'header': '/-\nCopyright (c) 2026 Team.\nAuthors: Original\n-/\n\n',
            'description': '# Topic\n', 'modern': True, 'authors': True, 'exposed_suffix': True}]})
        products = generated_files(self.root, self.config)
        expected = products['Lib/Topic.lean']
        self.assertIn('Authors: Ada, Grace', expected)
        self.assertTrue(expected.endswith('\n@[expose] public section\n'))
        (self.root / 'Lib/Topic.lean').write_text(expected)
        self.assertEqual(check_source(self.root, self.config, [leaf]), [])
        (self.root / 'Lib/Topic.lean').write_text('module\npublic import Lib.Topic.One\n')
        self.assertTrue(any('ownership' in error for error in check_source(self.root, self.config, [])))

    def test_exact_explained_token_exception_does_not_hide_other_tokens(self):
        key = self.source('Test.Control', 'axiom datum : Nat\ntheorem x : True := by sorry\n', 'support')
        self.policy('exceptions', {'schema': 1, 'kind': 'source_exceptions', 'token_exceptions': {'Test/Control.lean': {'axiom': 'Checker negative fixture'}}})
        errors = check_source(self.root, self.config, [key])
        self.assertEqual(len(errors), 1)
        self.assertIn('forbidden token sorry', errors[0])

    def test_budget_local_positive_explained_declaration(self):
        budget = {'max_heartbeats': 200000, 'require_local': True, 'explain': 'all', 'legacy': {}}
        good = 'set_option maxHeartbeats 400000 in\n-- Local synthesis needs extra search.\n@[simp] theorem t : True := by trivial\n'
        self.assertEqual(check_budget(good, 'Lib.lean', budget), [])
        for body in ['set_option maxHeartbeats 0x0 in\n-- reason\ntheorem t : True := by trivial',
                     'set_option maxHeartbeats 1 in\n-- reason\nsection',
                     'set_option maxHeartbeats 1 in\ntheorem t : True := by trivial',
                     'set_option maxHeartbeats 1',
                     'set_option maxHeartbeats 400000 in\n-- reason\nset_option maxHeartbeats 1 in section']:
            with self.subTest(body=body):
                self.assertTrue(check_budget(body, 'Lib.lean', budget))

    def test_r5_excess_and_finite_legacy_multisets(self):
        budget = {'max_heartbeats': 200000, 'require_local': False, 'explain': 'excess', 'legacy': {'Lib.lean': [500000]}}
        self.assertEqual(check_budget('set_option maxHeartbeats 1000\n', 'Lib.lean', budget), [])
        self.assertEqual(check_budget('-- bounded expensive declaration\nset_option maxHeartbeats 600000 in theorem t : True := by trivial', 'Lib.lean', budget), [])
        self.assertEqual(check_budget('set_option maxHeartbeats 400000\n', 'Lib.lean', budget), [])
        self.assertTrue(check_budget('set_option maxHeartbeats 400000\nset_option maxHeartbeats 300000', 'Lib.lean', budget))
        self.assertTrue(check_budget('set_option maxHeartbeats 0', 'Lib.lean', budget))
        self.assertEqual(check_budget('/- Finite elaboration allowance for this theorem. -/\nset_option maxHeartbeats 400000 in\ninclude purity in\ntheorem t : True := by trivial', 'Lib.lean', budget), [])

    def test_implementation_safety_is_role_policy_not_identifier_matching(self):
        key = self.source('Lib.One', 'theorem t : constant D = constant D := rfl\n')
        self.policy('style', {'schema': 1, 'kind': 'source', 'declaration_safety_roles': ['production']})
        self.assertEqual(check_source(self.root, self.config, [key]), [])
        self.source('Lib.One', 'constant unsupported : Nat\n')
        self.assertTrue(any('constant' in e for e in check_source(self.root, self.config, [key])))
        support = self.source('Tools.Driver', 'unsafe def main : IO Unit := pure ()\n', 'support')
        self.assertEqual(check_source(self.root, self.config, [support]), [])

    def test_unknown_required_profile_rejected(self):
        key = self.source('Lib.One', 'def x := 1\n')
        self.policy('style', {'schema': 1, 'kind': 'source', 'disable_budget': True})
        with self.assertRaisesRegex(ValueError, 'Unsupported'):
            check_source(self.root, self.config, [key])

    def test_references_are_not_executable_source_subjects(self):
        (self.root / 'historical.lean').write_text('import Missing.Source\naxiom old : False\n')
        self.config['extra_sources'] = [{'path': 'historical.lean', 'role': 'references'}]
        self.assertEqual(check_source(self.root, self.config, []), [])

    def test_control_failure_requires_real_expected_diagnostic(self):
        key = self.source('Test.Fail', 'example : False := by trivial\n', 'expected_failure')
        self.config['expected_failure'] = ['Test/Fail.lean']
        self.policy('controls', {'schema': 1, 'kind': 'controls', 'expected_failures': [
            {'path': 'Test/Fail.lean', 'contains': ['required rejection'], 'prerequisites': []}]})
        with patch('lean_ci.checks.native.lake_environment', return_value={'lean': 'lean', 'LEAN_PATH': ''}), patch('lean_ci.checks.guards.subprocess.run') as invoke:
            invoke.return_value.returncode = 1
            invoke.return_value.stderr = ''
            for diagnostic, wanted in [('Test.lean:1: error: wrong error', 1),
                                       ('Test.lean:1: error: required rejection', 0),
                                       ('Test.lean:1: error: required rejection; object file missing', 1)]:
                invoke.return_value.stdout = diagnostic
                with self.subTest(diagnostic=diagnostic):
                    self.assertEqual(run('expected-failure', self.root, [key], config=self.config, repo_root=self.root), wanted)

    def test_empty_control_selection_still_runs_mandatory_native_suite(self):
        with patch('lean_ci.checks.native.lake_environment', return_value={'lean': 'lean'}), patch('lean_ci.checks.native.run_native_controls', return_value=1) as suite:
            self.assertEqual(run('controls', self.root, [], config=self.config, repo_root=self.root), 1)
            suite.assert_called_once()

    def test_consumer_controls_compile_only_in_overlay(self):
        control = self.source('Test.Fixture', 'axiom unsupported : False\n', 'control')
        self.config['controls'] = ['Test/Fixture.lean']
        with patch('lean_ci.checks.native.lake_environment', return_value={'lean': 'lean', 'LEAN_PATH': ''}), patch('lean_ci.checks.native.run_native_controls', return_value=0), patch('lean_ci.checks.guards.subprocess.run') as invoke:
            invoke.return_value.returncode = 0
            invoke.return_value.stdout = invoke.return_value.stderr = ''
            self.assertEqual(run('controls', self.root, [control], config=self.config, repo_root=self.root), 0)
            output = Path(invoke.call_args.args[0][2])
            self.assertFalse(output.is_relative_to(self.root))
            self.assertFalse((self.root / '.lake/build/lib/lean/Test/Fixture.olean').exists())

    def test_builtin_is_selected_no_build_and_keeps_options_stable(self):
        key = self.source('Lib.One', 'def x := 1\n')
        with patch('lean_ci.checks.guards.subprocess.run') as invoke:
            invoke.return_value.returncode = 0
            self.assertEqual(run('builtin', self.root, [key], config=self.config, repo_root=self.root), 0)
        self.assertEqual(invoke.call_args.args[0], ['lake', '--no-build', 'lint', '--builtin-only', 'Lib.One'])
        self.assertEqual(invoke.call_args.kwargs['cwd'], self.root.resolve())


if __name__ == '__main__':
    unittest.main()
