"""Small Git/import fixtures and mocked native commands; never invoke Lean."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

from affected_scope import cache_roots, select, validate
from check_affected import execute
from run_style_linter import selected_driver
from run_declaration_linter import (MARKER, run as run_selected_declaration_linter,
                                    selected_driver as selected_declaration_driver)
from ci_audit import AUDIT_DRIVER
import ci_pipeline as core
import prepare_downstream
from test_ci_state import native_fixture, receipt


class AffectedScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aglib-scope-fixture-')
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        self.write('Aglib/Base.lean', 'module\ndef base := 1\n')
        self.write('Aglib/Dep.lean', 'module\npublic import Aglib.Base\ndef dependent := 1\n')
        self.write('Aglib/Cold.lean', 'module\ndef cold := 1\n')
        self.write('Aglib.lean', 'module\npublic import Aglib.Dep\npublic import Aglib.Cold\n')
        self.write('AglibTest/Focused.lean', 'import Aglib.Dep\nexample : True := trivial\n')
        self.write('AglibTest.lean', 'import AglibTest.Focused\n')
        self.write('AglibTest/AuditSupport.lean', 'import Lean\ndef support := 1\n')
        self.write('Audits/Aglib.lean',
                   (Path(__file__).resolve().parents[1] / 'Audits/Aglib.lean').read_text())
        self.write('AglibTest/AuditCoverage.lean', 'module\ndef coverage := 1\n')
        self.write('examples/downstream/Consumer/Use.lean', 'module\npublic import Aglib.Dep\ndef use := 1\n')
        self.write('examples/downstream/Consumer.lean', 'module\npublic import Consumer.Use\n')
        self.write('examples/downstream/Audit.lean', 'import Consumer\n')
        self.write('README.md', 'Fixture.\n')
        self.write('scripts/README.md', 'Fixture scripts.\n')
        self.write('docs/evidence.json', '{}\n')
        self.write(AUDIT_DRIVER, (Path(__file__).resolve().parents[1] / AUDIT_DRIVER).read_text())
        self.write('lean-toolchain', 'fixed\n')
        self.write('lakefile.toml', 'name = "Aglib"\n')
        self.write('lake-manifest.json', '{"name": "Aglib", "packages": []}\n')
        self.write('.gitignore', '.lake/\nInit.lean\nLean.lean\nLake.lean\nLake/\n')
        self.write('.lake/packages/batteries/scripts/runLinter.lean', 'import Batteries.Tactic.Lint\nimport Lake.CLI.Main\n')
        self.write('.lake/packages/mathlib/scripts/lint-style.lean', 'import Mathlib.Tactic.Linter.TextBased\nimport Cli.Basic\n')
        for name in ('Init', 'Lean', 'Lake', 'Lake.CLI.Main'):
            self.write(str(Path(*name.split('.')).with_suffix('.lean')), 'module\n')
            native_fixture(self.root, name)
        for package, name in [('batteries', 'Batteries.Tactic.Lint'),
                              ('Cli', 'Cli.Basic'), ('mathlib', 'Mathlib.Tactic.Linter.TextBased')]:
            owner = self.root / '.lake/packages' / package
            self.write(str((owner / Path(*name.split('.')).with_suffix('.lean')).relative_to(self.root)), 'import Lean\n')
            native_fixture(owner, name)
        for name in ['Aglib.Base', 'Aglib.Dep', 'Aglib.Cold', 'Aglib', 'AglibTest.Focused',
                     'AglibTest', 'AglibTest.AuditSupport', 'AglibTest.AuditCoverage']:
            native_fixture(self.root, name)
        prepare_downstream.prepare(self.root)
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'fixed fixture')
        self.base = self.git('rev-parse', 'HEAD').strip()

    def tearDown(self):
        self.temp.cleanup()

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True)

    def changed_plan(self):
        self.write('Aglib/Base.lean', 'module\ndef base := 2\n')
        return select(self.root, self.base)

    def test_actual_affected_graph_keeps_consumers_without_cold_siblings(self):
        plan = self.changed_plan()
        self.assertEqual(plan['providers'], ['Aglib.Base'])
        self.assertEqual(plan['consumers'], ['Aglib', 'Aglib.Dep'])
        self.assertEqual(plan['tests'], ['AglibTest', 'AglibTest.Focused'])
        self.assertEqual(plan['client'], ['Consumer', 'Consumer.Use'])
        self.assertNotIn('Aglib.Cold', plan['providers'] + plan['consumers'])
        self.assertNotIn('Audits.Aglib', plan['tests'])
        self.assertIn('Aglib.Cold', plan['imports']['Aglib'])
        self.assertEqual(plan['style'], ['Aglib.Base'])
        self.assertEqual(plan['coverage'], 'affected-only')

    def test_changed_facade_is_compiled_consumer(self):
        self.write('Aglib.lean', 'module\npublic import Aglib.Dep\n')
        plan = select(self.root, self.base)
        self.assertEqual(plan['consumers'], ['Aglib'])
        self.assertEqual(plan['providers'], [])
        self.assertTrue(plan['native'])

    def test_ci_lean_files_select_native_tooling_without_production_enrollment(self):
        for path in ('ci/lean/SelectedAudit.lean', 'ci/fixtures/quartz/Check.lean'):
            with self.subTest(path=path):
                self.write(path, 'import Lean\n')
                plan = select(self.root, self.base)
                self.assertFalse(plan['native'])
                self.assertTrue(plan['trust'] and plan['controls'])
                self.assertIn('lean-ci', plan['tooling_tests'])
                self.assertEqual(plan['providers'] + plan['consumers'] + plan['tests'], [])

    def test_deleted_ci_lean_file_remains_a_native_tooling_change(self):
        path = 'ci/fixtures/quartz/Check.lean'
        self.write(path, 'import Aglib.Base\n')
        self.git('add', '--', path)
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'fixed CI fixture')
        base = self.git('rev-parse', 'HEAD').strip()
        (self.root / path).unlink()
        plan = select(self.root, base)
        self.assertFalse(plan['native'])
        self.assertTrue(plan['controls'])
        self.assertEqual(plan['providers'] + plan['consumers'] + plan['tests'], [])

    def test_verified_base_keeps_proof_changes_after_later_tooling_commit(self):
        self.write('Aglib/Base.lean', 'module\ndef base := 2\n')
        self.git('add', 'Aglib/Base.lean')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'proof with unfinished CI')
        previous_push = self.git('rev-parse', 'HEAD').strip()
        self.write('scripts/cache_ci.py', '# repair tooling after failed proof CI\n')
        self.git('add', 'scripts/cache_ci.py')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'tooling repair')
        pending = select(self.root, self.base, head='HEAD')
        self.assertIn('Aglib.Base', pending['providers'])
        self.assertTrue(pending['native'])
        self.assertTrue(pending['trust'])
        self.assertIn('AglibTest.Focused', pending['tests'])
        self.assertFalse(select(self.root, previous_push, head='HEAD')['native'])

    def test_deleted_and_renamed_provider_retain_old_dependents(self):
        (self.root / 'Aglib/Base.lean').rename(self.root / 'Aglib/New.lean')
        plan = select(self.root, self.base)
        self.assertEqual(plan['providers'], ['Aglib.New'])
        self.assertIn('Aglib.Dep', plan['consumers'])
        self.assertIn('Aglib/Base.lean', plan['changed'])
        self.assertIn('Aglib/New.lean', plan['changed'])

    def test_docs_and_evidence_json_run_only_static_checks(self):
        self.write('README.md', '[evidence](docs/evidence.json)\n')
        self.write('docs/evidence.json', '{"status": "partial"}\n')
        self.write('scripts/README.md', 'Changed script documentation.\n')
        plan = select(self.root, self.base)
        self.assertFalse(plan['native'])
        calls = []
        output = Path(self.temp.name) / 'no-export.jsonl'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            summary = execute(self.root, plan, None, outputs=output)
        self.assertEqual(len(calls), 4)
        self.assertEqual(summary['native_validation'], 'not-performed')
        self.assertFalse(output.exists())
        self.assertFalse(any('lake' in command for command in calls))
        self.assertEqual(cache_roots(self.root, plan), [])


    def test_routine_cache_projection_excludes_client_and_control_dependencies(self):
        self.write('Aglib/Base.lean', 'module\npublic import Mathlib.Provider\ndef base := 1\n')
        self.write('Aglib/Cold.lean', 'module\npublic import Mathlib.FacadeDependency\ndef cold := 1\n')
        self.write('examples/downstream/Consumer/Use.lean',
                   'import Aglib.Dep\nimport Mathlib.Client\ndef use := 1\n')
        self.write('AglibTest/AuditCoverage.lean', 'import Mathlib.Trust\n')
        self.write('AglibTest/NegativeControls/ImportedAudit.lean',
                   'import AglibTest.AuditSupport\nimport Mathlib.Trust\n\n'
                   'run_cmd do\n  let count ← IO.pure 0\n')
        self.write('.lake/packages/batteries/Batteries/Tactic/Lint.lean', 'import Mathlib.ToolDependency\n')
        self.write('.lake/packages/Cli/Cli/Basic.lean', 'import Init\n')
        for name in ('Provider', 'FacadeDependency', 'Client', 'Trust', 'ToolDependency',
                     'Tactic/Linter/TextBased'):
            self.write('.lake/packages/mathlib/Mathlib/' + name + '.lean', 'import Init\n')
        self.write('.lake/packages/mathlib/Mathlib/Unrelated.lean', 'import Init\n')
        plan = select(self.root, self.base)
        self.assertTrue(plan['controls'])
        self.assertEqual(cache_roots(self.root, plan),
                         ['Mathlib.FacadeDependency', 'Mathlib.Provider',
                          'Mathlib.Tactic.Linter.TextBased', 'Mathlib.ToolDependency', 'Mathlib.Trust'])
        self.assertNotIn('Mathlib.Unrelated', plan['cache_imports'])
        # The selected Aglib facade really imports Cold; its cache basis stays present.
        self.assertIn('Mathlib.FacadeDependency', plan['cache_imports'])

    def test_cache_projection_rejects_missing_pinned_tooling_without_default_fetch(self):
        plan = self.changed_plan()
        (self.root / '.lake/packages/mathlib/scripts/lint-style.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing pinned linter source'):
            cache_roots(self.root, plan)

    def test_tooling_selects_its_affected_fixture_tests_without_lean(self):
        self.write('scripts/affected_scope.py', '# changed selector fixture\n')
        plan = select(self.root, self.base)
        self.assertFalse(plan['native'])
        self.assertEqual(plan['tooling_tests'], ['test_affected_scope'])

    def test_new_tooling_paths_require_explicit_regression_selection(self):
        for path in ('scripts/new_helper.py', 'scripts/nested/check_kernel.py'):
            with self.subTest(path=path):
                self.write(path, '# unassigned helper\n')
                with self.assertRaisesRegex(ValueError, 'assign its regression scope explicitly'):
                    select(self.root, self.base)
                (self.root / path).unlink()

    def test_missing_base_unknown_path_and_pin_fail_closed(self):
        with self.assertRaises(ValueError):
            select(self.root)
        with self.assertRaises(subprocess.CalledProcessError):
            select(self.root, 'missing-base')
        self.write('unknown.toml', 'unknown = true\n')
        with self.assertRaisesRegex(ValueError, 'Unrecognized changed path'):
            select(self.root, self.base)
        (self.root / 'unknown.toml').unlink()
        self.write('lean-toolchain', 'another pin\n')
        with self.assertRaisesRegex(ValueError, 'Configuration/pin'):
            select(self.root, self.base)

    def test_zero_before_uses_true_initial_diff_or_available_merge_base(self):
        initial = select(self.root, '0' * 40, head='HEAD')
        self.assertIn('Aglib.Base', initial['providers'])
        self.assertNotEqual(initial['base'], self.base)
        self.write('Aglib/Base.lean', 'module\ndef base := 2\n')
        self.git('add', 'Aglib/Base.lean')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'branch fixture')
        selected = select(self.root, '0' * 40, head='HEAD', default_base=self.base)
        self.assertEqual(selected['base'], self.base)
        self.assertEqual(selected['providers'], ['Aglib.Base'])
        with self.assertRaisesRegex(ValueError, 'New-branch event'):
            select(self.root, '0' * 40, head='HEAD')

    def test_new_unselected_change_invalidates_plan(self):
        plan = self.changed_plan()
        self.write('Aglib/Cold.lean', 'module\ndef changedCold := 1\n')
        with self.assertRaisesRegex(ValueError, 'scope drifted'):
            validate(self.root, plan)

    def test_selected_input_drift_rejects_plan(self):
        plan = self.changed_plan()
        self.write('Aglib/Dep.lean', 'module\ndef changed := 1\n')
        with self.assertRaisesRegex(ValueError, 'Plan input changed'):
            validate(self.root, plan)

    def native_mock(self, calls, failure=None):
        def command(task, directory):
            args = list(map(str, task['command']))
            calls.append([task['id'], *args])
            if failure and (failure in task['id'] or any(failure in arg for arg in args)):
                raise subprocess.CalledProcessError(19, args)
            directory.mkdir(parents=True, exist_ok=True)
            cwd = Path(task['cwd'])
            if task['id'] == 'prepare-client':
                prepare_downstream.prepare(self.root)
            if task['kind'] in ('build', 'graph-build'):
                for name in task['modules']:
                    native_fixture(cwd, name)
            value = {'receipt': receipt(args, cwd)}
            if task['kind'] == 'environment':
                paths = list(dict.fromkeys([str(cwd / '.lake/build/lib/lean'), str(self.root / '.lake/build/lib/lean'), *[
                    str(self.root / '.lake/packages' / name / '.lake/build/lib/lean')
                    for name in ('batteries', 'Cli', 'mathlib')]]))
                Path(task['environment_output']).write_text(':'.join(paths) + '\n')
                value.update(search_path=paths, output_sha256=core.file_hash(task['environment_output']))
            if task.get('identity_modules'):
                value['native_modules'] = {name: core.module_identity(cwd, name)
                                           for name in task['identity_modules']}
            if task.get('mapping'):
                Path(task['mapping']).write_text('"2026-03-17"\n' +
                    json.dumps(['0123456789abcdef', {'fixture': 'native mapping'}]) + '\n')
                value['mapping_sha256'] = core.file_hash(task['mapping'])
            return value
        identity = {'lean': 'fixture', 'lake': 'fixture', 'installation': '/fixture/runtime'}
        return SimpleNamespace(root=self.root, run=command, compiler_identity=lambda *a, **k: identity)


    def test_routine_and_full_task_plans_do_not_schedule_diagnostic_chains(self):
        plans = [self.changed_plan(), select(self.root, full=True)]
        for scope in plans:
            with self.subTest(coverage=scope['coverage']):
                tasks = core.tasks(self.root, {'scope': scope}, 'check',
                                   Path(self.temp.name) / 'planned')
                ids = {task['id'] for task in tasks}
                self.assertTrue({'shared-root-build', 'Aglib/declaration',
                                 'AglibTest/declaration', 'audit/all', 'check_placeholders.py'} <= ids)
                self.assertFalse({'prepare-client', 'client/build', 'client-audit',
                                  'negative-controls', 'compiled-inventory',
                                  'core-native-cache'} & ids)
                self.assertFalse(any('check_kernel.py' in task['command'] for task in tasks))
        diagnostics = core.tasks(self.root, {'scope': plans[-1]}, 'native',
                                 Path(self.temp.name) / 'diagnostics', phases=['trust', 'client'])
        ids = {task['id'] for task in diagnostics}
        self.assertTrue({'prepare-client', 'audit/all', 'compiled-inventory',
                         'negative-controls', 'client-audit'} <= ids)

    def test_local_final_uses_one_graph_accepted_umbrellas_and_no_build_export(self):
        plan, calls = self.changed_plan(), []
        directory = Path(self.temp.name) / 'run'
        output = directory / 'selected.jsonl'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            summary = execute(self.root, plan, directory, native_only=True, ci=True, outputs=output)
        ids = [command[0] for command in calls]
        self.assertEqual(ids.count('shared-root-build'), 1)
        self.assertLess(ids.index('shared-root-build'), ids.index('Aglib/declaration'))
        self.assertLess(ids.index('Aglib/declaration'), ids.index('AglibTest/declaration'))
        self.assertEqual(ids.count('audit/all'), 1)
        for diagnostic in ('negative-controls', 'compiled-inventory', 'prepare-client', 'client/build', 'client-audit'):
            self.assertNotIn(diagnostic, ids)
        self.assertEqual(ids[-1], 'root-graph')
        self.assertEqual(calls[-1][1:5], ['lake', '--rehash', '--no-build', 'build'])
        self.assertTrue(any('Aglib.Cold' in command and command[0] == 'unrelated-cached-imports' for command in calls))
        self.assertEqual(summary['declaration_policy']['tests'], 'AglibTest umbrella when present; otherwise exact selected positive origins in one native batch')
        self.assertEqual(json.loads(output.read_text().splitlines()[0]), '2026-03-17')
        self.assertNotIn('Aglib.Cold', summary['selected_targets'])


    def test_umbrella_lint_failure_stops_audit_client_and_export(self):
        plan, calls = self.changed_plan(), []
        directory = Path(self.temp.name) / 'run'
        output = directory / 'selected.jsonl'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls, 'Aglib/declaration')):
            with self.assertRaises(subprocess.CalledProcessError):
                execute(self.root, plan, directory, native_only=True, ci=True, outputs=output)
        self.assertFalse(output.exists())
        self.assertFalse(any(command[0] in ('audit/all', 'client/build', 'root-graph') for command in calls))


    def test_local_category_repair_keeps_umbrella_predicates_without_proof_builds(self):
        plan, calls = self.changed_plan(), []
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True,
                    ci=True, phases=['provider-lint'])
        builtin = [command for command in calls if '--builtin-only' in command]
        self.assertEqual([command[-1] for command in builtin], ['Aglib', 'AglibTest'])
        self.assertFalse(any(command[0] in ('shared-root-build', 'client/build', 'audit/all') for command in calls))
        declarations = [command for command in calls if '--run' in command]
        self.assertEqual([command[-1] for command in declarations], ['Aglib', 'AglibTest'])
        self.assertTrue(any(command[0] == 'shared-root-cached' and '--no-build' in command for command in calls))


    def test_local_builtin_failure_stops_remaining_umbrella_categories(self):
        plan, calls = self.changed_plan(), []
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls, 'AglibTest/builtin')):
            with self.assertRaises(subprocess.CalledProcessError):
                execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True,
                        ci=True, phases=['provider-lint'])
        self.assertEqual([command[-1] for command in calls if '--builtin-only' in command], ['Aglib', 'AglibTest'])
        self.assertFalse(any('--run' in command for command in calls))


    def test_cold_facade_import_fails_without_build_fallback(self):
        plan, calls = self.changed_plan(), []
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls, 'unrelated-cached-imports')):
            with self.assertRaises(subprocess.CalledProcessError):
                execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True, ci=True)
        self.assertFalse(any(command[0] == 'shared-root-build' for command in calls))


    def test_provider_build_repair_does_not_run_check_or_client_groups(self):
        plan, calls = self.changed_plan(), []
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True,
                    ci=True, phases=['providers'])
        graphs = [command for command in calls if command[0] == 'shared-root-build']
        self.assertEqual(len(graphs), 1)
        self.assertNotIn('Aglib', graphs[0][1:])
        self.assertFalse(any('--run' in command or command[0] == 'client/build' for command in calls))


    def test_native_local_check_does_not_require_prepared_client(self):
        plan, calls = self.changed_plan(), []
        (self.root / 'examples/downstream/.lake/packages').unlink()
        (self.root / 'examples/downstream/.lake').rmdir()
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True)
        self.assertNotIn('prepare-client', [call[0] for call in calls])

    def test_source_policy_only_check_does_not_discover_a_native_toolchain(self):
        self.write('scripts/check_source_policy.py', '# changed static source policy\n')
        plan, calls = select(self.root, self.base), []
        self.assertFalse(plan['native'])
        runtime = self.native_mock(calls)
        with patch('check_affected.NativeRuntime', return_value=runtime), \
                patch.object(runtime, 'compiler_identity') as compiler:
            summary = execute(self.root, plan, Path(self.temp.name) / 'source')
        compiler.assert_not_called()
        self.assertEqual(summary['native_validation'], 'not-performed')
        self.assertFalse(any('lake' in command for command in calls))

    def test_local_retry_reuses_completed_umbrella_checks_after_later_failure(self):
        plan, calls = self.changed_plan(), []
        state = Path(self.temp.name) / 'retry'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls, 'AglibTest/declaration')):
            with self.assertRaises(subprocess.CalledProcessError):
                execute(self.root, plan, state, native_only=True)
        self.assertFalse((state / 'complete.json').exists())
        calls.clear()
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            summary = execute(self.root, plan, state, native_only=True)
        self.assertIn('Aglib/declaration', summary['reused_checks'])
        self.assertNotIn('Aglib/declaration', [command[0] for command in calls])
        self.assertIn('AglibTest/declaration', [command[0] for command in calls])

    def test_client_audit_uses_client_environment_and_reuses_after_later_failure(self):
        plan, calls = self.changed_plan(), []
        state = Path(self.temp.name) / 'client-retry'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls, 'root-graph')):
            with self.assertRaises(subprocess.CalledProcessError):
                execute(self.root, plan, state, native_only=True, phases=['providers', 'provider-lint', 'consumers', 'client'])
        record = json.loads((state / 'local.json').read_text())
        checked = next(item for item in record['tasks'] if item['id'] == 'client-audit')
        binding = checked['result']['success']['binding']
        self.assertIn('Consumer', binding['native'])
        self.assertIn('Audit.lean', binding['raw_inputs'])
        self.assertIn('Consumer', binding['reflective_imports']['roots'])
        self.assertEqual(binding['execution']['cwd'], 'examples/downstream')
        calls.clear()
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            summary = execute(self.root, plan, state, native_only=True, phases=['providers', 'provider-lint', 'consumers', 'client'])
        self.assertIn('client-audit', summary['reused_checks'])
        self.assertNotIn('client-audit', [command[0] for command in calls])

    def test_changed_client_audit_source_invalidates_its_success(self):
        plan, calls = self.changed_plan(), []
        state = Path(self.temp.name) / 'client-source'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, state, native_only=True, phases=['providers', 'provider-lint', 'consumers', 'client'])
        self.write('examples/downstream/Audit.lean', 'import Consumer\n-- changed audit input\n')
        current = select(self.root, self.base)
        calls.clear()
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            summary = execute(self.root, current, state, native_only=True, phases=['providers', 'provider-lint', 'consumers', 'client'])
        self.assertIn('client-audit', summary['performed_checks'])
        self.assertIn('client-audit', [command[0] for command in calls])

    def test_selector_reads_observed_source_even_when_bytes_are_restored(self):
        plan, calls = self.changed_plan(), []
        original = core.AglibLocalAdapter.select_scope
        def mutate(adapter, root, **kwargs):
            path = root / 'Aglib/Cold.lean'
            content = path.read_bytes()
            path.write_bytes(content + b'\n')
            path.write_bytes(content)
            return original(adapter, root, **kwargs)
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)), \
                patch.object(core.AglibLocalAdapter, 'select_scope', mutate):
            with self.assertRaises(core.InputDrift if hasattr(core, 'InputDrift') else ValueError):
                execute(self.root, plan, Path(self.temp.name) / 'drift', native_only=True)
        self.assertEqual(calls, [])

    def test_local_and_ci_construct_the_same_native_policy_recipe(self):
        plan = {'scope': self.changed_plan()}
        directory = Path(self.temp.name) / 'recipe'
        local = core.tasks(self.root, plan, 'check', directory)
        native = core.tasks(self.root, plan, 'native', directory)
        self.assertEqual([task for task in local if task.get('native') is not False], native)
        self.assertEqual([task['modules'] for task in native if task.get('check_kind') == 'declaration'],
                         [['Aglib'], ['AglibTest']])

    def test_style_adapter_preserves_checks_options_and_exact_module_enumeration(self):
        source = ('options\n  -- Get all the imports, but only those in the same package.\n'
                  '  let allModuleNames ← originModules.flatMapM expandImports\n'
                  '  -- Read the `nolints` file\n'
                  '  lintModules opts nolints allModuleNames\n  undocumentedScripts opts\n')
        selected = selected_driver(source)
        self.assertIn('let allModuleNames := originModules', selected)
        self.assertIn('lintModules opts nolints allModuleNames', selected)
        self.assertIn('undocumentedScripts opts', selected)
        with self.assertRaises(ValueError):
            selected_driver('unexpected driver revision')

    def test_declaration_adapter_keeps_enabled_checks_and_exact_module_filter(self):
        source = ('preamble\n' + MARKER
                  + '    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)\n'
                  + '    let results ← lintCore decls linters\n'
                  + '    if failed then IO.Process.exit 1\n')
        selected = selected_declaration_driver(source)
        self.assertIn('lintEnv.getModuleIdxFor? name', selected)
        self.assertIn('lintEnv.header.moduleNames[index.toNat]! == module', selected)
        self.assertIn('getChecks (slow := true) (runAlways := none) (runOnly := none)', selected)
        self.assertIn('lintCore decls linters', selected)
        self.assertIn('if failed then IO.Process.exit 1', selected)
        with self.assertRaises(ValueError):
            selected_declaration_driver('unrecognized driver')

    def test_declaration_lint_uses_one_runtime_for_all_exact_origins(self):
        source = 'preamble\n' + MARKER + '    let linters ← getChecks\n'
        self.write('.lake/packages/batteries/scripts/runLinter.lean', source)
        modules = ['Aglib.Dep', 'Aglib.Base']
        calls = []

        def command(args, cwd):
            self.assertEqual(cwd, self.root)
            self.assertEqual(args[:4], ['lake', 'env', 'fixture-lean', '--run'])
            self.assertEqual(Path(args[4]).read_text(), selected_declaration_driver(source))
            self.assertEqual(args[5:], ['--no-build', *modules])
            calls.append(args)
            return subprocess.CompletedProcess(args, 0)

        with patch.dict(os.environ, {'LEAN': 'fixture-lean'}), \
                patch('run_declaration_linter.subprocess.run', side_effect=command):
            self.assertEqual(run_selected_declaration_linter(self.root, modules), 0)
        self.assertEqual(len(calls), 1)
        self.assertFalse(Path(calls[0][4]).exists())

    def test_declaration_lint_batch_failure_propagates_without_retry(self):
        self.write('.lake/packages/batteries/scripts/runLinter.lean', 'preamble\n' + MARKER)
        modules = ['Aglib.Base', 'Aglib.Dep', 'Aglib.Cold']
        calls = []

        def command(args, cwd):
            calls.append(args)
            return subprocess.CompletedProcess(args, 19)

        with patch('run_declaration_linter.subprocess.run', side_effect=command):
            self.assertEqual(run_selected_declaration_linter(self.root, modules), 19)
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][5:], ['--no-build', *modules])
        self.assertFalse(Path(calls[0][4]).exists())

    def test_no_test_umbrella_uses_selected_positive_origins_and_keeps_axioms(self):
        (self.root / 'AglibTest.lean').unlink()
        plan = self.changed_plan()
        required = core.tasks(self.root, {'scope': plan}, 'check',
                              Path(self.temp.name) / 'no-umbrella')
        declaration = next(t for t in required if t['id'] == 'AglibTest/declaration')
        self.assertEqual(declaration['modules'], ['AglibTest.Focused'])
        self.assertEqual(declaration['command'],
                         ['python3', 'scripts/run_declaration_linter.py', 'AglibTest.Focused'])
        self.assertFalse(any('AglibTest' in t['command'] for t in required))
        self.assertEqual(sum(t['id'] == 'audit/all' for t in required), 1)
        audit = next(t for t in required if t['id'] == 'audit/all')
        self.assertEqual(json.loads(audit['command'][-1]),
                         [['Aglib'], ['AglibTest', 'Focused']])
        self.assertFalse(any(t['id'] in {'prepare-client', 'client/build', 'negative-controls',
                                        'compiled-inventory'} for t in required))

    def test_client_only_changes_have_source_only_default_tasks(self):
        self.write('examples/downstream/Consumer/Use.lean',
                   'module\npublic import Aglib.Dep\ndef use := 2\n')
        self.write('examples/downstream/lean-toolchain', 'client-only-toolchain\n')
        plan = select(self.root, self.base)
        self.assertFalse(plan['native'])
        self.assertFalse(plan['publish'])
        self.assertFalse(plan['trust'])
        self.assertEqual(plan['cache_imports'], [])
        self.assertEqual(core.AglibAdapter().required_phases(self.root, {'scope': plan}), ['source'])
        tasks = core.tasks(self.root, {'scope': plan}, 'check', Path(self.temp.name) / 'client-only')
        self.assertTrue(tasks)
        self.assertTrue(all(not task['native'] for task in tasks))
        self.assertFalse(any('lake' in task['command'] or task['kind'] == 'environment'
                             or 'client' in task['id'] for task in tasks))
        calls = []
        runtime = self.native_mock(calls)
        with patch('check_affected.NativeRuntime', return_value=runtime), \
                patch.object(runtime, 'compiler_identity') as compiler:
            result = execute(self.root, plan, Path(self.temp.name) / 'client-check')
        compiler.assert_not_called()
        self.assertEqual(result['native_validation'], 'not-performed')

    def test_changed_audit_support_retains_origin_audit_without_automatic_kernel_replay(self):
        self.write('AglibTest/AuditSupport.lean', 'import Lean\ndef support := 2\n')
        plan, calls = select(self.root, self.base), []
        directory = Path(self.temp.name) / 'run'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, directory, native_only=True, phases=['trust'])
        self.assertFalse((directory / 'SelectedAudit.lean').exists())
        audit = (self.root / AUDIT_DRIVER).read_text()
        self.assertEqual(audit.count('import AglibTest.AuditSupport'), 1)
        audit_call = next(command for command in calls if AUDIT_DRIVER in command)
        self.assertEqual(json.loads(audit_call[-1]), [['Aglib'], ['AglibTest']])
        self.assertIn('AglibAudit.auditModules selected', audit)
        self.assertIn('coverage.contains `AuditForeign.GeneratedDatum.rec', audit)
        self.assertIn('unless hidden.size == 1', audit)
        self.assertIn('(env.checked.get.find? hidden[0]!).isSome', audit)
        self.assertFalse(any('scripts/check_kernel.py' in ' '.join(c) for c in calls))
        self.assertTrue(any('scripts/check_compiled_inventory.py' in ' '.join(c) for c in calls))

    def test_changed_proof_reuses_controls_but_keeps_selected_trust_coverage(self):
        plan, calls = self.changed_plan(), []
        self.assertTrue(plan['trust'])
        self.assertFalse(plan['controls'])
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True, phases=['trust'])
        text = [' '.join(command) for command in calls]
        self.assertTrue(any('/SelectedAudit.lean' in command for command in text))
        self.assertTrue(any('check_compiled_inventory.py --modules Aglib.Base' in command for command in text))
        self.assertFalse(any('check_kernel.py' in command for command in text))
        self.assertFalse(any('check_negative_controls.py' in command for command in text))

    def test_ordinary_local_checks_export_without_diagnostics(self):
        plan, calls = self.changed_plan(), []
        directory = Path(self.temp.name) / 'run'
        output = directory / 'outputs.jsonl'
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, directory, native_only=True, outputs=output)
        text = [' '.join(command) for command in calls]
        self.assertFalse(any('check_kernel.py' in command for command in text))
        self.assertEqual(sum(command[0] == 'audit/all' for command in calls), 1)
        for diagnostic in ('check_compiled_inventory.py', 'client-audit', 'prepare_downstream.py'):
            self.assertFalse(any(diagnostic in command for command in text))
        coverage = json.loads(output.with_suffix('.jsonl.coverage.json').read_text())
        self.assertEqual(coverage['kernel_replay'],
                         'not-requested; standalone diagnostic only')
        self.assertEqual(coverage['negative_controls'],
                         'not-selected')
        self.assertNotIn('independent_replay', coverage)

    def test_auditor_controls_and_runtime_changes_trigger_rejection_controls(self):
        inputs = ['AglibTest/AuditSupport.lean', 'Audits/Aglib.lean',
                  'AglibTest/AuditCoverage.lean', 'AglibTest/NegativeControls/ImportedFixture.lean',
                  'scripts/check_negative_controls.py', 'scripts/resource_guard.py', 'scripts/build_serial.py']
        for path in inputs:
            with self.subTest(path=path):
                target = self.root / path
                previous = target.read_text() if target.exists() else None
                self.write(path, (previous or '') + '\n-- changed control input\n')
                plan = select(self.root, self.base)
                self.assertTrue(plan['controls'])
                self.assertTrue(plan['trust'])
                self.assertEqual(plan['native'], path == 'AglibTest/AuditCoverage.lean')
                if not plan['native']:
                    tasks = core.tasks(self.root, {'scope': plan}, 'check',
                                       Path(self.temp.name) / 'control-only')
                    self.assertTrue(all(not task['native'] for task in tasks))
                if previous is None:
                    target.unlink()
                else:
                    target.write_text(previous)
        self.write('scripts/check_negative_controls.py', '# changed checker\n')
        plan, calls = select(self.root, self.base), []
        with patch('check_affected.NativeRuntime', return_value=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True, ci=True, phases=['trust'])
        self.assertTrue(any('scripts/check_negative_controls.py' in command for command in calls))

    def test_workflow_calls_the_current_native_recipe_without_legacy_pipeline(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        self.assertIn('uses: ./.github/workflows/lean-ci.yml', workflow)
        self.assertIn('package-directory: .', workflow)
        self.assertIn('build-targets: Aglib', workflow)
        self.assertIn('contents: read', workflow)
        self.assertIn('contents: write', workflow)
        self.assertIn('cancel-in-progress: false', workflow)
        self.assertIn('queue: max', workflow)
        for obsolete in ('scripts/ci_pipeline.py', 'scripts/build_serial.py',
                         'prepare_downstream.py', 'check_kernel.py', 'github.event.before'):
            self.assertNotIn(obsolete, workflow)


if __name__ == '__main__':
    unittest.main()
