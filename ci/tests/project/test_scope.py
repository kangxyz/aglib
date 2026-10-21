"""Affected selection across additions, removals and package boundaries."""
from lean_ci.project.configuration import load_config
from lean_ci.project.scope import select_scope
from tests.project.test_configuration import Fixture


class ScopeTests(Fixture):
    def test_leaf_selects_providers_consumers_tests_facade_without_expansion(self):
        base = self.commit()
        self.write('Tiny/Base.lean', 'module\ndef base := 2\n')
        scope = select_scope(self.root, base=base)
        self.assertEqual(scope['providers'], ['Tiny.Base'])
        self.assertEqual(scope['consumers'], ['Tiny', 'Tiny.Consumer'])
        self.assertEqual(scope['tests'], ['TinyTest.Positive'])
        self.assertEqual(scope['source_style'], ['Tiny.Base'])
        self.assertNotIn('Tiny', scope['declarations'])
        self.assertIn('Tiny', scope['modules'])

    def test_test_only_does_not_select_production(self):
        self.commit()
        self.write('TinyTest/Positive.lean', 'import Tiny.Consumer\nexample : consumer = 1 := rfl\n-- edit\n')
        scope = select_scope(self.root)
        self.assertEqual(scope['providers'] + scope['consumers'], [])
        self.assertEqual(scope['tests'], ['TinyTest.Positive'])

    def test_old_edge_union_preserves_removed_import_consumers(self):
        base = self.commit()
        (self.root / 'Tiny/Base.lean').unlink()
        self.write('Tiny/Consumer.lean', 'def consumer := 2\n')
        scope = select_scope(self.root, base=base)
        self.assertIn('Tiny.Base', scope['removed'])
        self.assertIn('Tiny.Consumer', scope['providers'])
        self.assertIn('TinyTest.Positive', scope['tests'])

    def test_rename_keeps_both_identities(self):
        self.commit()
        (self.root / 'Tiny/Base.lean').rename(self.root / 'Tiny/Renamed.lean')
        scope = select_scope(self.root)
        self.assertIn('Tiny.Base', scope['removed'])
        self.assertIn('Tiny.Renamed', scope['providers'])
        self.assertIn('Tiny.Consumer', scope['consumers'])

    def test_documentation_and_tooling_do_not_build_mathematics(self):
        self.commit()
        self.write('README.md', 'Documentation\n')
        self.write('ci/report.py', 'print("report")\n')
        scope = select_scope(self.root)
        self.assertFalse(scope['native'])
        self.assertEqual(scope['modules'], [])
        self.assertEqual(scope['tooling'], ['ci/report.py'])

    def test_initialization_keeps_whole_current_universe(self):
        self.commit()
        initial = select_scope(self.root, initial=True)
        self.assertEqual(initial['base'], None)
        self.assertEqual(set(initial['modules']), set(load_config(self.root)['modules']))
        self.write('TinyTest/Positive.lean', '-- repair\nimport Tiny.Consumer\n')
        repaired = select_scope(self.root, initial=True)
        self.assertEqual(initial['modules'], repaired['modules'])
        self.assertEqual(repaired['coverage'], 'current-obligation-universe')

    def test_explicit_target_is_narrow_but_actual_consumers_follow(self):
        self.commit()
        self.write('Tiny/Other.lean', 'def other := 4\n')
        scope = select_scope(self.root, targets=['Tiny.Consumer'])
        self.assertNotIn('Tiny.Other', scope['modules'])
        self.assertEqual(scope['providers'], ['Tiny.Consumer'])
        self.assertEqual(scope['source_style'], ['Tiny.Consumer'])

    def test_unknown_target_rejected(self):
        self.commit()
        with self.assertRaisesRegex(ValueError, 'No current'):
            select_scope(self.root, targets=['Absent'])

    def test_modern_quoted_imports_use_shared_lexer(self):
        self.write('Tiny/Consumer.lean', 'module\npublic meta import all Tiny.«Base»\ndef consumer := base\n')
        self.commit()
        self.write('Tiny/Base.lean', 'module\ndef base := 2\n')
        self.assertIn('Tiny.Consumer', select_scope(self.root)['consumers'])

    def test_invalidated_compiler_option_is_named(self):
        self.commit()
        path = self.root / 'lakefile.toml'
        path.write_text(path.read_text().replace('name="Tiny"\n[[lean_lib]]', 'name="Tiny"\n[leanOptions]\nmaxHeartbeats=200000\n[[lean_lib]]', 1))
        scope = select_scope(self.root)
        self.assertEqual(scope['invalidations'][0]['kind'], 'compiler-options-or-enrollment')
        self.assertEqual(scope['invalidations'][0]['path'], 'lakefile.toml')

    def test_package_qualified_client_uses_dependency_edge(self):
        from tests.project.test_configuration import ConfigurationTests
        ConfigurationTests.add_client(self)
        self.commit()
        self.write('Tiny/Base.lean', 'def base := 2\n')
        scope = select_scope(self.root)
        self.assertEqual(scope['clients'], {'downstream': ['downstream:Consumer']})

    def test_policy_change_selects_checks_without_math_build(self):
        self.write('policy/nolints.json', '[]\n')
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('[policy]\nnolints=["policy/nolints.json"]\n')
        self.commit()
        self.write('policy/nolints.json', '[[]]\n')
        scope = select_scope(self.root)
        self.assertEqual(scope['modules'], [])
        self.assertEqual(set(scope['check_only']['declarations']), {'Tiny.Base', 'Tiny.Consumer', 'TinyTest.Positive'})
        self.assertTrue(scope['native'])

    def test_common_native_tool_smoke_does_not_build_math(self):
        self.commit()
        self.write('ci/src/lean_ci/native.py', '# runtime change\n')
        scope = select_scope(self.root)
        self.assertTrue(scope['common_controls'])
        self.assertEqual(scope['modules'], [])

    def test_examples_compile_when_affected(self):
        self.write('Demo/Example.lean', 'import Tiny.Base\ndef sample := base\n')
        with (self.root / 'lakefile.toml').open('a') as stream:
            stream.write('[[lean_lib]]\nname="Demo"\n')
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('examples=["Demo"]\n')
        self.commit()
        self.write('Tiny/Base.lean', 'def base := 2\n')
        scope = select_scope(self.root)
        self.assertEqual(scope['auxiliary'], ['Demo.Example'])
        self.assertNotIn('Demo.Example', scope['tests'])

    def add_dependency(self, revision):
        import json
        self.write('lakefile.toml', 'name="Tiny"\n[[lean_lib]]\nname="Tiny"\n[[lean_lib]]\nname="TinyTest"\n[[require]]\nname="external"\ngit="https://example.invalid/external"\nrev="' + revision + '"\n')
        self.write('lake-manifest.json', json.dumps({'packages': [{'name': 'external', 'type': 'git', 'rev': revision, 'inputRev': revision, 'url': 'https://example.invalid/external', 'inherited': False}]}))

    def test_missing_dependency_sources_is_explicit_setup_gap(self):
        from lean_ci.project.scope import DependencySourcesUnavailable
        self.add_dependency('a' * 40)
        self.commit()
        self.add_dependency('b' * 40)
        with self.assertRaises(DependencySourcesUnavailable) as failure:
            select_scope(self.root)
        self.assertEqual(failure.exception.dependency, 'external')
        self.assertEqual(failure.exception.path, '.')
        # Explicit local coverage remains executable without claiming the whole
        # dependency transition was assessed.
        selected = select_scope(self.root, targets=['Tiny.Base'])
        self.assertEqual(selected['providers'], ['Tiny.Base'])
        self.assertEqual(selected['invalidations'][0]['basis'],
                         'explicit-targets; dependency-transition-unassessed')

    def test_resolved_lean_lake_dependency_uses_actual_source_namespace(self):
        import subprocess
        self.write('.gitignore', '.lake/\n')
        dependency = self.root / '.lake/packages/external'
        dependency.mkdir(parents=True)
        def git(*args):
            return subprocess.check_output(['git', *args], cwd=dependency,
                                           stderr=subprocess.DEVNULL).decode().strip()
        def commit():
            git('add', '.')
            git('-c', 'user.name=CI fixture', '-c', 'user.email=ci@example.invalid',
                '-c', 'commit.gpgSign=false', 'commit', '-qm', 'dependency fixture')
            return git('rev-parse', 'HEAD')
        git('init', '-q')
        self.write('.lake/packages/external/lakefile.lean', 'import Lake\n')
        self.write('.lake/packages/external/External.lean', 'import External.Base\n')
        self.write('.lake/packages/external/External/Base.lean', 'def foreign := 1\n')
        self.add_dependency(commit())
        self.write('Tiny/Base.lean', 'import External.Base\ndef base := 1\n')
        self.write('Tiny/Unrelated.lean', 'import Init\ndef unrelated := 1\n')
        self.commit()
        self.write('.lake/packages/external/External/Base.lean', 'def foreign := 2\n')
        self.add_dependency(commit())
        selected = select_scope(self.root)
        self.assertIn('Tiny.Base', selected['providers'])
        self.assertNotIn('Tiny.Unrelated', selected['modules'])
        self.assertEqual(selected['invalidations'][0]['basis'], 'pinned-external-import-closure')

    def test_changed_compile_pass_control_is_native_but_not_positive_test(self):
        self.write('TinyTest/Control.lean', 'def control := 1\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'controls=["TinyTest/Control.lean"]\n[roles]'))
        self.commit()
        self.write('TinyTest/Control.lean', 'def control := 2\n')
        selected = select_scope(self.root)
        self.assertTrue(selected['native'])
        self.assertEqual(selected['controls'], ['TinyTest/Control.lean'])
        self.assertEqual(selected['modules'], [])

    def test_expected_failure_reselected_when_its_provider_changes(self):
        self.write('TinyTest/Negative.lean', 'import Tiny.Base\n#check missing\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'expected_failure=["TinyTest/Negative.lean"]\n[roles]'))
        self.commit()
        self.write('Tiny/Base.lean', 'def base := 2\n')
        selected = select_scope(self.root)
        self.assertEqual(selected['expected_failure'], ['TinyTest/Negative.lean'])
        self.assertNotIn('TinyTest.Negative', selected['tests'])


class ConfigurationDeltaTests(Fixture):
    def test_comment_and_role_order_are_semantic_noops(self):
        self.commit()
        path = self.root / '.github/lean-ci.toml'
        path.write_text('# comment only\n' + path.read_text().replace('production=["Tiny"]\ntests=["TinyTest"]', 'tests=["TinyTest"]\nproduction=["Tiny"]'))
        scope = select_scope(self.root)
        self.assertEqual(scope['enrollment_changes'], [])
        self.assertEqual(scope['policy_changes'], {})
        self.assertEqual(scope['source_check'], [])
        self.assertEqual(scope['modules'], [])
        self.assertFalse(scope['native'])

    def test_removing_existing_nolints_reference_selects_native_checks_only(self):
        self.write('policy/nolints.json', '[]\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text() + '[policy]\nnolints=["policy/nolints.json"]\n')
        self.commit()
        path.write_text(path.read_text().replace('nolints=["policy/nolints.json"]', 'nolints=[]'))
        scope = select_scope(self.root)
        self.assertEqual(set(scope['check_only']['declarations']), {'Tiny.Base', 'Tiny.Consumer', 'TinyTest.Positive'})
        self.assertEqual(scope['modules'], [])
        self.assertEqual(scope['source_style'], [])
        self.assertEqual(scope['source_check'], [])
        self.assertEqual(scope['policy_changes']['nolints']['after'], [])

    def test_heartbeat_allowance_removal_inspects_unchanged_source(self):
        import json
        from lean_ci.checks.guards import check_source
        self.write('Tiny/Base.lean', 'set_option maxHeartbeats 300000\ndef base := 1\n')
        budget = {'schema': 1, 'kind': 'budget', 'max_heartbeats': 200000,
                  'require_local': False, 'explain': 'excess', 'legacy': {'Tiny/Base.lean': [300000]}}
        self.write('policy/budget.json', json.dumps(budget))
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text() + '[policy]\nbudget=["policy/budget.json"]\n')
        self.commit()
        self.assertEqual(check_source(self.root, load_config(self.root), ['Tiny.Base']), [])
        budget['legacy'] = {}
        self.write('policy/budget.json', json.dumps(budget))
        scope = select_scope(self.root)
        errors = check_source(self.root, load_config(self.root), scope['source_check'])
        self.assertTrue(any('maxHeartbeats 300000 exceeds' in error for error in errors))
        self.assertEqual(scope['source_style'], [])
        self.assertEqual(scope['modules'], [])
        self.assertFalse(scope['native'])

    def test_support_promotion_uses_old_role_and_new_test_obligations(self):
        from lean_ci.project.scope import snapshot
        self.write('Helpers/Proof.lean', 'import Tiny.Base\ndef helper := base\n')
        self.write('TinyTest/HelperUsage.lean', 'import Helpers.Proof\nexample : helper = 1 := rfl\n')
        with (self.root / 'lakefile.toml').open('a') as stream:
            stream.write('[[lean_lib]]\nname="Helpers"\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text() + 'support=["Helpers"]\n')
        base = self.commit()
        path.write_text(path.read_text().replace('tests=["TinyTest"]', 'tests=["TinyTest", "Helpers"]').replace('support=["Helpers"]', 'support=[]'))
        config = load_config(self.root)
        self.assertEqual(snapshot(self.root, config, base)['Helpers.Proof']['role'], 'support')
        scope = select_scope(self.root, config)
        self.assertEqual(scope['tests'], ['Helpers.Proof', 'TinyTest.HelperUsage'])
        self.assertNotIn('Tiny.Base', scope['modules'])
        change = next(x for x in scope['enrollment_changes'] if x['path'] == 'Helpers/Proof.lean')
        self.assertEqual(change['before']['role'], 'support')
        self.assertEqual(change['after']['role'], 'tests')
        self.assertIn('compile', change['added_obligations'])
        self.assertIn('Helpers.Proof', scope['source_check'])

    def test_client_id_change_preserves_historical_package_coordinates(self):
        from tests.project.test_configuration import ConfigurationTests
        from lean_ci.project.scope import historical_config, snapshot
        ConfigurationTests.add_client(self)
        base = self.commit()
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('id="downstream"', 'id="renamed"'))
        config = load_config(self.root)
        before = historical_config(self.root, config, base)
        self.assertEqual(before['workspaces'][1]['id'], 'downstream')
        old = snapshot(self.root, config, base)
        self.assertIn('downstream:Consumer', old)
        self.assertNotIn('renamed:Consumer', old)
        scope = select_scope(self.root, config)
        self.assertEqual(scope['clients'], {'renamed': ['renamed:Consumer']})
        change = next(x for x in scope['enrollment_changes'] if x['path'] == 'examples/downstream/Consumer.lean')
        self.assertEqual(change['before']['key'], 'downstream:Consumer')
        self.assertEqual(change['after']['key'], 'renamed:Consumer')
        # Move the independent package under a production namespace. Its
        # sources must not become phantom root-package modules.
        (self.root / 'examples/downstream').rename(self.root / 'Tiny/client')
        path.write_text(path.read_text().replace('path="examples/downstream"', 'path="Tiny/client"'))
        moved = load_config(self.root)
        self.assertEqual(snapshot(self.root, moved, base)['downstream:Consumer']['path'], 'examples/downstream/Consumer.lean')
        self.assertNotIn('Tiny.client.Consumer', snapshot(self.root, moved))
        moved_scope = select_scope(self.root, moved)
        self.assertEqual(moved_scope['clients'], {'renamed': ['renamed:Consumer']})
        # An ancestor package must not exclude its nested client's records.
        import shutil
        (self.root / 'package').mkdir()
        for name in ('Tiny', 'TinyTest', 'Tiny.lean', 'lakefile.toml', 'lean-toolchain'):
            shutil.move(str(self.root / name), str(self.root / 'package' / name))
        path.write_text(path.read_text().replace('package_dir="."', 'package_dir="package"').replace('path="Tiny/client"', 'path="package/Tiny/client"'))
        nested = load_config(self.root)
        nested_graph = snapshot(self.root, nested)
        self.assertEqual(nested_graph['renamed:Consumer']['package_path'], 'package/Tiny/client')
        self.assertEqual(select_scope(self.root, nested)['clients'], {'renamed': ['renamed:Consumer']})

    def test_valid_demotion_reports_removed_obligations_and_current_consumers(self):
        self.write('Stable/Unrelated.lean', 'def unrelated := 0\n')
        with (self.root / 'lakefile.toml').open('a') as stream:
            stream.write('[[lean_lib]]\nname="Stable"\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('production=["Tiny"]', 'production=["Tiny", "Stable"]'))
        self.commit()
        path.write_text(path.read_text().replace('production=["Tiny", "Stable"]', 'production=["Stable"]').replace('tests=["TinyTest"]', 'tests=["TinyTest"]\nsupport=["Tiny"]'))
        scope = select_scope(self.root)
        self.assertEqual(scope['tests'], ['TinyTest.Positive'])
        self.assertNotIn('Stable.Unrelated', scope['modules'])
        self.assertNotIn('Tiny.Base', scope['modules'])
        self.assertIn('Tiny.Base', scope['source_check'])
        change = next(x for x in scope['enrollment_changes'] if x['path'] == 'Tiny/Base.lean')
        self.assertEqual(change['before']['role'], 'production')
        self.assertEqual(change['after']['role'], 'support')
        self.assertIn('compile', change['removed_obligations'])

    def test_ordered_budget_policy_references_preserve_precedence(self):
        import json
        from lean_ci.checks.guards import check_source
        self.write('Tiny/Base.lean', 'set_option maxHeartbeats 250000\ndef base := 1\n')
        for name, cap in [('low', 200000), ('high', 300000)]:
            self.write('policy/' + name + '.json', json.dumps({'schema': 1, 'kind': 'budget', 'max_heartbeats': cap,
                'require_local': False, 'explain': 'excess', 'legacy': {}}))
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text() + '[policy]\nbudget=["policy/low.json", "policy/high.json"]\n')
        self.commit()
        self.assertEqual(check_source(self.root, load_config(self.root), ['Tiny.Base']), [])
        path.write_text(path.read_text().replace('["policy/low.json", "policy/high.json"]', '["policy/high.json", "policy/low.json"]'))
        scope = select_scope(self.root)
        self.assertIn('budget', scope['policy_changes'])
        self.assertTrue(any('maxHeartbeats 250000 exceeds' in e for e in check_source(self.root, load_config(self.root), scope['source_check'])))
        self.assertEqual(scope['modules'], [])
        self.assertEqual(scope['source_style'], [])
