"""Focused setup/cache boundaries; commands and network are mocked."""
import json
from contextlib import contextmanager
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from urllib.error import HTTPError, URLError

from lean_ci.transport import cache as cache_transport
from lean_ci.execution import prepare
from lean_ci.project.configuration import PIN
from lean_ci.project.source import module_path


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.package = self.root
        self.revision = 'a' * 40
        self.write('.github/lean-ci.toml', 'schema = 1\n[roles]\nproduction = ["Project"]\ntests = ["ProjectTest"]\n')
        self.write('lakefile.toml', 'name = "Project"\n[[lean_lib]]\nname = "Project"\n[[lean_lib]]\nname = "ProjectTest"\n')
        self.write('lean-toolchain', PIN + '\n')
        self.write('Project.lean', 'import Project.Leaf\n')
        self.write('Project/Leaf.lean', 'import Up.Provider\n')
        self.write('ProjectTest.lean', 'import Project.Leaf\n')
        self.manifest = {'name': 'Project', 'packagesDir': '.lake/packages', 'packages': [
            {'type': 'git', 'name': 'up', 'url': 'https://github.com/owner/up.git', 'rev': self.revision, 'inherited': False},
            {'type': 'git', 'name': 'mathlib', 'url': 'https://github.com/leanprover-community/mathlib4.git', 'rev': self.revision, 'inherited': False},
            {'type': 'git', 'name': 'batteries', 'url': 'https://github.com/leanprover-community/batteries', 'rev': self.revision, 'inherited': True}]}
        self.write('lake-manifest.json', json.dumps(self.manifest))
        for package, modules in {
            'up': {'Up.Provider': 'import Up.Deep', 'Up.Deep': 'import Mathlib.Needed'},
            'mathlib': {'Mathlib.Needed': 'import Mathlib.Unneeded', 'Mathlib.Unneeded': '',
                        'Mathlib.Tactic.Linter.TextBased': '', 'Mathlib.StyleRuntime': ''},
            'batteries': {'Batteries.Tactic.Lint': 'import Batteries.Shared', 'Batteries.Shared': '',
                          'Batteries.Data.String.Basic': '', 'Cli.Basic': '', 'ImportGraph.Imports.FromSource': ''},
        }.items():
            for module, source in modules.items():
                self.write(str(Path('.lake/packages') / package / module_path(module)), source + '\n')
        self.write('.lake/packages/mathlib/scripts/lint-style.lean', 'import Mathlib.StyleRuntime\n')
        self.write('.lake/packages/mathlib/lake-manifest.json', json.dumps({'packages': [self.manifest['packages'][2]]}))
        self.scope = {'native': True, 'modules': ['Project.Leaf'], 'source_style': [],
                      'declarations': ['Project.Leaf'], 'controls': [], 'expected_failure': [],
                      'coverage': 'explicit-targets'}
        self.commands = []
        self.pins = patch.object(prepare.subprocess, 'check_output',
                                 side_effect=lambda command, **kwargs: '' if command[1] == 'status' else self.revision)
        self.pins.start(); self.addCleanup(self.pins.stop)
        self.runner = patch.object(prepare, '_run', side_effect=self.run_command)
        self.runner.start(); self.addCleanup(self.runner.stop)

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def run_command(self, command, cwd, directory, label, environment, resource_config, **kwargs):
        self.commands.append((command, cwd, label, kwargs))
        return {'command': command, 'receipt': str(directory / (label + '.json'))}

    def test_static_scope_does_no_dependency_or_cache_work(self):
        result = prepare.prepare(self.root, scope={'native': False, 'coverage': 'static'})
        self.assertFalse(result['native'])
        self.assertEqual(self.commands, [])
        self.assertFalse((self.root / '.lake/lean-ci').exists())

    def test_scoped_imports_follow_external_package_but_stop_at_mathlib_root(self):
        result = prepare.prepare(self.root, scope=self.scope, environment={})
        self.assertEqual(result['imports']['mathlib'], ['Mathlib.Needed'])
        self.assertEqual(result['imports']['external'], ['Batteries.Shared', 'Batteries.Tactic.Lint', 'Mathlib.Needed', 'Up.Deep', 'Up.Provider'])
        self.assertEqual([row[2] for row in self.commands], ['resolve-deps', 'native-assets', 'mathlib-cache', 'dependency-imports'])
        self.assertIn('owner/up', self.commands[1][0])
        self.assertEqual(self.commands[2][0], ['Batteries.Shared', 'Batteries.Tactic.Lint', 'Mathlib.Needed'])
        self.assertTrue(self.commands[2][3]['cache'])
        probe = self.commands[3][0]
        self.assertEqual(probe[:4], ['lake', '--rehash', '--no-build', 'build'])
        self.assertNotIn('+Project.Leaf:leanArts', probe)
        self.assertEqual(result['coverage'], 'setup-only; no mathematical compilation or checker success')

    def test_hosted_workflow_owns_public_asset_restore(self):
        result = prepare.prepare(self.root, scope=self.scope, environment={'GITHUB_ACTIONS': 'true'})
        self.assertEqual(result['native_assets'], 'workflow-action')
        self.assertNotIn('native-assets', [row[2] for row in self.commands])

    def test_source_style_needs_imports_without_subject_olean(self):
        self.write('.lake/packages/batteries/Cli/Basic.lean', 'import Batteries.OptionalPrerequisite\n')
        self.write('.lake/packages/batteries/Batteries/OptionalPrerequisite.lean', '')
        self.scope.update(modules=[], declarations=[], source_style=['Project.Leaf'])
        result = prepare.prepare(self.root, scope=self.scope, environment={})
        self.assertIn('Mathlib.StyleRuntime', result['imports']['mathlib'])
        self.assertIn('Mathlib.Needed', result['imports']['mathlib'])
        self.assertFalse((self.root / '.lake/build/lib/lean/Project/Leaf.olean').exists())
        self.assertNotIn('Project.Leaf', result['imports']['runtime'])
        self.assertEqual(result['imports']['source_runtime'], ['Cli.Basic', 'ImportGraph.Imports.FromSource'])
        probe = next(command for command, _, label, _ in self.commands if label == 'dependency-imports')
        self.assertNotIn('+Cli.Basic:leanArts', probe)
        self.assertNotIn('+ImportGraph.Imports.FromSource:leanArts', probe)
        self.assertIn('+Batteries.OptionalPrerequisite:leanArts', probe)

    def test_pin_drift_fails_even_when_native_command_succeeds(self):
        def mutate(*args, **kwargs):
            self.write('lake-manifest.json', '{}')
            return {}
        with patch.object(prepare, '_run', side_effect=mutate):
            with self.assertRaisesRegex(ValueError, 'changed pinned configuration'):
                prepare.prepare(self.root, scope=self.scope)
        self.assertEqual(json.loads((self.root / 'lake-manifest.json').read_text()), {})

    def test_real_command_failure_is_not_a_cache_miss_or_build_permission(self):
        with patch.object(prepare, '_run', side_effect=ValueError('HTTP 403')):
            with self.assertRaisesRegex(ValueError, 'HTTP 403'):
                prepare.prepare(self.root, scope=self.scope)
        self.assertEqual(self.commands, [])

    def test_missing_or_ambiguous_reachable_source_fails(self):
        self.write('.lake/packages/up/Up/Deep.lean', 'import Unknown.Module\n')
        with self.assertRaisesRegex(ValueError, 'Missing/ambiguous.*Unknown.Module'):
            prepare.prepare(self.root, scope=self.scope)
        self.assertEqual([row[2] for row in self.commands], ['resolve-deps'])

    def test_existing_dependency_must_match_committed_revision(self):
        with patch.object(prepare.subprocess, 'check_output', return_value='b' * 40):
            with self.assertRaisesRegex(ValueError, 'differs from committed pin'):
                prepare.prepare(self.root, scope=self.scope, fetch=False)

    def test_dirty_dependency_sources_cannot_claim_a_pinned_basis(self):
        with patch.object(prepare.subprocess, 'check_output',
                          side_effect=lambda command, **kwargs: ' M Up/Provider.lean' if command[1] == 'status' else self.revision):
            with self.assertRaisesRegex(ValueError, 'source checkout is dirty'):
                prepare.prepare(self.root, scope=self.scope, fetch=False)

    def test_policy_only_origin_and_common_controls_prepare_runtime_without_building_subjects(self):
        self.scope.update(modules=[], declarations=[], check_only={'axioms': ['Project.Leaf']}, common_controls=True)
        result = prepare.prepare(self.root, scope=self.scope, fetch=False)
        self.assertIn('Batteries.Tactic.Lint', result['imports']['runtime'])
        self.assertIn('Mathlib.Needed', result['imports']['mathlib'])
        self.assertNotIn('+Project.Leaf:leanArts', self.commands[0][0])

    def test_changed_init_only_control_prepares_fixed_control_runtime_without_math_roots(self):
        self.write('ProjectTest/Control.lean', 'import Init\nimport Lean\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'controls=["ProjectTest/Control.lean"]\n[roles]'))
        self.scope.update(modules=[], declarations=[], controls=['ProjectTest/Control.lean'], common_controls=False)
        config = prepare.load_config(self.root)
        dependencies = prepare._dependency_sources(self.root, self.manifest)
        result = prepare.required_imports(self.root, config, self.scope, dependencies)
        self.assertTrue(set(prepare.native.runtime_roots('controls')) <= set(result['runtime']))
        self.assertIn('Batteries.Tactic.Lint', result['cache_roots'])
        self.assertEqual(result['mathlib'], [])
        self.assertFalse(any(name.startswith('Mathlib.') for name in result['cache_roots']))
        self.assertEqual(self.commands, [])

    def test_missing_dependency_sources_for_selection_resolves_once_then_reselects(self):
        unavailable = prepare.DependencySourcesUnavailable('root', '.', 'up')
        with patch.object(prepare, 'select_scope', side_effect=[unavailable, self.scope]) as selection, \
                patch.object(prepare, 'local_base', return_value='fixture-base'), \
                patch.object(prepare, 'resolve_planning_sources', return_value={'status': 'sources-ready'}) as sources:
            prepare.prepare(self.root, requested_base='fixture-base')
        self.assertEqual(selection.call_count, 2)
        sources.assert_called_once()
        self.assertEqual([row[2] for row in self.commands].count('resolve-deps'), 1)

    def test_arbitrary_selection_failure_never_launches_dependency_resolution(self):
        with patch.object(prepare, 'select_scope', side_effect=ValueError('invalid ownership')):
            with self.assertRaisesRegex(ValueError, 'invalid ownership'):
                prepare.prepare(self.root)
        self.assertEqual(self.commands, [])

    def test_offline_preparation_never_resolves_or_downloads(self):
        result = prepare.prepare(self.root, scope=self.scope, fetch=False, environment={})
        self.assertEqual(result['native_assets'], 'offline')
        self.assertEqual([row[2] for row in self.commands], ['dependency-imports'])

    def add_client(self):
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('\n[[clients]]\nid = "downstream"\npath = "examples/downstream"\n[clients.roles]\nproduction = ["Consumer"]\n')
        self.write('examples/downstream/lakefile.toml', 'name = "client"\n[[lean_lib]]\nname = "Consumer"\n[[require]]\nname = "Project"\npath = "../.."\n')
        self.write('examples/downstream/lean-toolchain', PIN + '\n')
        self.write('examples/downstream/Consumer.lean', 'import Project.Leaf\n')
        client = json.loads(json.dumps(self.manifest))
        for item in client['packages']:
            item['inherited'] = True
        client['packages'].append({'type': 'path', 'name': 'Project', 'dir': '../..', 'inherited': False})
        client['name'] = 'client'
        self.write('examples/downstream/lake-manifest.json', json.dumps(client, indent=3) + '\n')
        return self.root / 'examples/downstream/lake-manifest.json'

    def test_independent_client_shares_only_matching_parent_pins(self):
        path = self.add_client()
        before = path.stat().st_mtime_ns, path.read_bytes()
        self.scope.update(modules=['downstream:Consumer'], declarations=['downstream:Consumer'])
        result = prepare.prepare(self.root, scope=self.scope, fetch=False)
        self.assertEqual(result['imports']['mathlib'], ['Mathlib.Needed'])
        self.assertEqual((path.stat().st_mtime_ns, path.read_bytes()), before)
        self.assertEqual((path.parent / '.lake/packages').resolve(), self.root / '.lake/packages')

    def test_different_client_pin_and_redirected_store_are_rejected(self):
        path = self.add_client()
        document = json.loads(path.read_text())
        document['packages'][0]['rev'] = 'b' * 40
        path.write_text(json.dumps(document))
        with self.assertRaisesRegex(ValueError, 'Client manifest differs'):
            prepare.prepare(self.root, scope=self.scope, fetch=False)

    def test_missing_client_manifest_is_materialized_from_exact_pins(self):
        path = self.add_client()
        path.unlink()
        result = prepare.prepare(self.root, scope=self.scope, fetch=False)
        self.assertTrue(result['clients'][0]['manifest_created'])
        document = json.loads(path.read_text())
        self.assertEqual(document['packages'][0]['rev'], self.revision)
        self.assertTrue(document['packages'][0]['inherited'])
        self.assertEqual(document['packages'][-1]['dir'], '../..')

    def test_only_obsolete_package_owned_facets_are_pruned(self):
        self.write('.lake/build/lib/lean/Project/Leaf.olean.private.hash', 'retained')
        self.write('.lake/build/lib/lean/Project/Deleted.olean', 'obsolete')
        self.write('.lake/build/ir/Project/Deleted.c.o', 'obsolete')
        self.write('.lake/packages/up/.lake/build/lib/lean/Up/Deleted.olean', 'dependency untouched')
        result = prepare.prepare(self.root, scope=self.scope, fetch=False)
        self.assertEqual(result['project_outputs'][0]['obsolete_facets_removed'], 2)
        self.assertTrue((self.root / '.lake/build/lib/lean/Project/Leaf.olean.private.hash').is_file())
        self.assertTrue((self.root / '.lake/packages/up/.lake/build/lib/lean/Up/Deleted.olean').is_file())

    def test_redirected_build_cache_fails_before_any_prune(self):
        self.write('.lake/build/lib/lean/Project/Deleted.olean', 'obsolete')
        (self.root / '.lake/build/lib/lean/alias').symlink_to(self.root)
        with self.assertRaisesRegex(ValueError, 'Symlink in package-owned build'):
            prepare.prepare(self.root, scope=self.scope, fetch=False)
        self.assertTrue((self.root / '.lake/build/lib/lean/Project/Deleted.olean').is_file())

    def test_nested_package_coordinates_do_not_assume_git_root_is_lake_root(self):
        # Move only project/source data; its exact manifest and dependencies remain
        # local to the configured package instead of the repository root.
        package = self.root / 'lean'
        package.mkdir()
        for name in ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json', 'Project.lean', 'ProjectTest.lean', 'Project', '.lake'):
            (self.root / name).rename(package / name)
        self.write('.github/lean-ci.toml', 'schema = 1\npackage_dir = "lean"\n[roles]\nproduction = ["Project"]\ntests = ["ProjectTest"]\n')
        result = prepare.prepare(self.root, scope=self.scope, environment={})
        self.assertEqual(self.commands[0][1], package)
        self.assertEqual(result['imports']['mathlib'], ['Mathlib.Needed'])


class PinnedTransportTests(unittest.TestCase):
    def test_only_http_404_is_classified_as_unpublished(self):
        dependency = [('Up', 'Up', 'owner/up', 'a' * 40)]
        with patch.object(cache_transport, 'identity', return_value={}), \
                patch.object(cache_transport, 'dependencies', return_value=dependency), \
                patch.object(cache_transport, 'public_asset', return_value='https://fixture/asset'), \
                patch.object(cache_transport, 'import_candidate', side_effect=HTTPError('url', 404, 'absent', {}, None)):
            self.assertEqual(cache_transport.restore_pinned(Path('.'), ['owner/up'])[0]['status'], 'not-published')
        for error in (URLError('network down'), ValueError('bad provenance'), HTTPError('url', 403, 'denied', {}, None)):
            with patch.object(cache_transport, 'identity', return_value={}), \
                    patch.object(cache_transport, 'dependencies', return_value=dependency), \
                    patch.object(cache_transport, 'public_asset', return_value='https://fixture/asset'), \
                    patch.object(cache_transport, 'import_candidate', side_effect=error):
                with self.assertRaises(type(error)):
                    cache_transport.restore_pinned(Path('.'), ['owner/up'])


class GuardedPreparationTests(unittest.TestCase):
    def test_no_unqualified_cache_download_can_escape_the_child_boundary(self):
        with patch.object(prepare.subprocess, 'call') as command:
            with self.assertRaisesRegex(ValueError, 'unscoped'):
                prepare._cache_child('/managed/lean', [], False)
            with self.assertRaises(ValueError):
                prepare._cache_child('/managed/lean', ['--all'], False)
        command.assert_not_called()

    def test_cache_bootstrap_preserves_managed_concurrency_and_loaded_package(self):
        for managed in (False, True):
            with self.subTest(managed=managed), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                budget = {'lean_threads': 4, 'remote_profile': {'jobs': 12}} if managed else {'lean_threads': 1}
                @contextmanager
                def capped(*args, **kwargs):
                    yield {'LEAN': '/managed/lean', 'PYTHONPATH': 'relative-ci'}
                with patch.object(prepare.resources, 'limits', return_value=budget), \
                        patch.object(prepare.build, 'build_threads', return_value=4 if managed else 1), \
                        patch.object(prepare.build, 'capped_toolchain', side_effect=capped), \
                        patch.object(prepare.resources, 'run', return_value=0) as run:
                    prepare._run(['Mathlib.Selected'], directory, directory, 'cache', {}, None, cache=True)
                command = run.call_args.args[0]
                self.assertEqual(command[command.index('--cache-child') + 1:],
                                 ['/managed/lean', 'managed' if managed else 'serialized', 'Mathlib.Selected'])
                self.assertTrue(run.call_args.kwargs['env']['PYTHONPATH'].startswith(str(Path(prepare.__file__).resolve().parents[2])))
                self.assertEqual(run.call_args.kwargs['budget']['native_build_threads'], 4 if managed else 1)

    def test_managed_child_does_not_serialize_or_modify_managed_wrapper(self):
        with patch.object(prepare.subprocess, 'call', return_value=0) as call, \
                patch.object(prepare.subprocess, 'check_output') as metadata, \
                patch.object(prepare, '_serialized_frontend') as serialized:
            self.assertEqual(prepare._cache_child('/managed/lean', ['Mathlib.Selected'], False), 0)
        call.assert_called_once_with(['lake', 'exe', 'cache', 'get', 'Mathlib.Selected'])
        metadata.assert_not_called(); serialized.assert_not_called()

    def test_local_temporary_wrapper_is_restored_after_failed_cache_command(self):
        with tempfile.TemporaryDirectory() as temporary:
            lean = Path(temporary) / 'lean'
            lean.write_text('original capped wrapper')
            with self.assertRaisesRegex(ValueError, 'failure'):
                with prepare._serialized_frontend(lean, {'--githash': b'fixture'}):
                    self.assertIn('LOCK_EX', lean.read_text())
                    raise ValueError('failure')
            self.assertEqual(lean.read_text(), 'original capped wrapper')


if __name__ == '__main__':
    unittest.main()
