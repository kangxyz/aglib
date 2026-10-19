"""Real committed Git fixtures and command adapters; never run Lean."""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import ci_pipeline as core
from ci_state import InputDrift, Progress, TemporalInputs, file_hash, locate_module, module_identity, read_json, write_json
import prepare_downstream
from test_ci_baseline import FixtureAPI, FULL, FULL_RECIPE, REPOSITORY
from test_ci_state import native_fixture, receipt


TOOLCHAIN = {'lean': 'fixture-lean-sha256', 'lake': 'fixture-lake-sha256',
             'installation': '/fixture/pinned-compiler-installation'}


class Commands:
    def __init__(self, root, fail=None, empty=None):
        self.root, self.fail, self.empty = root, fail, empty
        self.calls = []

    def run(self, task, directory):
        self.calls.append(task)
        if task['id'] == self.fail:
            raise ValueError('Actual command failed: ' + task['id'])
        if task['id'] == self.empty:
            return {}
        directory.mkdir(parents=True, exist_ok=True)
        cwd = Path(task['cwd'])
        if task['id'] == 'prepare-client':
            prepare_downstream.prepare(self.root)
        if task.get('generated'):
            Path(task['command'][-1]).write_text(task['generated'])
        if task['kind'] in ('graph-build', 'build'):
            for name in task['modules']:
                native_fixture(cwd, name)
            if task['kind'] == 'graph-build':
                for name in core.runtime_imports(self.root):
                    package = locate_module(self.root, name)
                    native_fixture(package, name)
        value = {'receipt': receipt(task['command'], cwd)}
        if task['kind'] == 'environment':
            paths = [str(self.root / '.lake/build/lib/lean'),
                     str(self.root / '.lake/packages/batteries/.lake/build/lib/lean'),
                     str(self.root / '.lake/packages/Cli/.lake/build/lib/lean')]
            Path(task['environment_output']).write_text(':'.join(paths) + '\n')
            value['search_path'] = paths
            value['output_sha256'] = file_hash(task['environment_output'])
        if task.get('identity_modules'):
            for name in task['identity_modules']:
                path = cwd / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.trace')
                if not path.is_file():
                    native_fixture(cwd, name)
            value['native_modules'] = {n: module_identity(cwd, n) for n in task['identity_modules']}
        if task.get('mapping'):
            Path(task['mapping']).write_text('{"native":"Lake-generated mapping fixture"}\n')
            value['mapping_sha256'] = file_hash(task['mapping'])
        return value


class PipelineTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aglib-ci-core-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        self.state = Path(self.temp.name) / 'state'
        self.progress = Path(self.temp.name) / 'check-progress'
        self.write('.gitignore', '.lake/\nexamples/downstream/.lake/\n')
        self.write('Aglib/Base.lean', 'module\ndef x := 1\n')
        for name in ('Init', 'Lean', 'Lake'):
            self.write(name + '.lean', 'module\n')
            native_fixture(self.root, name)
        self.write('Lean/Data/Json/Parser.lean', 'module\nimport Init\n')
        native_fixture(self.root, 'Lean.Data.Json.Parser')
        self.write('Aglib/Cold.lean', 'module\ndef cold := 1\n')
        self.write('Aglib.lean', 'module\npublic import Aglib.Base\npublic import Aglib.Cold\n')
        self.write('AglibTest/Positive.lean', 'module\nimport Aglib.Base\nexample : True := trivial\n')
        self.write('AglibTest.lean', 'module\nimport AglibTest.Positive\n')
        for path in ('AglibTest/Axioms.lean', 'AglibTest/AuditSupport.lean', 'AglibTest/AuditCoverage.lean'):
            self.write(path, (core.ROOT / path).read_text())
        self.write('examples/downstream/Consumer/Use.lean', 'module\nimport Aglib.Base\ndef y := 1\n')
        self.write('examples/downstream/Consumer.lean', 'module\nimport Consumer.Use\n')
        self.write('examples/downstream/Audit.lean', 'import Consumer\n')
        self.write('lean-toolchain', 'pinned\n')
        self.write('lakefile.toml', 'name = "Aglib"\n')
        self.write('lake-manifest.json', '{"name": "aglib", "packages": []}\n')
        self.write('README.md', 'Initial documentation.\n')
        self.write('.github/workflows/ci.yml', FULL)
        for path in core.POLICY:
            if path in core.FIXED_AUDIT_SOURCES:
                self.write(path, (core.ROOT / path).read_text())
            elif path.startswith('scripts/'):
                self.write(path, '# fixed checker fixture\n')
        for path in core.PACKAGE_SOURCES:
            self.write(path, (core.ROOT / path).read_text())
        self.write('scripts/check.sh', FULL_RECIPE)
        self.write('scripts/check_compiled_inventory.py', '# fixed inventory checker fixture\n')
        self.write(core.DRIVERS[0], 'import Batteries.Tactic.Lint\n')
        self.write(core.DRIVERS[1], 'import Cli.Basic\n')
        self.write('.lake/packages/batteries/Batteries/Tactic/Lint.lean', 'import Lean\n')
        self.write('.lake/packages/Cli/Cli/Basic.lean', 'import Lean\n')
        prepare_downstream.prepare(self.root)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.anchor = self.commit('whole-native anchor')
        legacy_heads = patch.object(core.ci_baseline, 'REVIEWED_LEGACY_HEADS', frozenset({self.anchor}))
        legacy_heads.start()
        self.addCleanup(legacy_heads.stop)
        run = {'id': 12, 'run_attempt': 1, 'head_sha': self.anchor,
               'status': 'completed', 'conclusion': 'success', 'head_branch': 'main',
               'event': 'push', 'head_repository': {'full_name': REPOSITORY},
               'path': '.github/workflows/ci.yml', 'html_url': 'https://github.com/fixture/aglib/actions/runs/12'}
        job = {'name': 'library', 'status': 'completed', 'conclusion': 'success',
               'steps': [{'name': core.ci_baseline.NATIVE_STEP, 'status': 'completed', 'conclusion': 'success'}]}
        self.api = FixtureAPI([run], {'/actions/runs/12/attempts/1/jobs': [job]})

    def write(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def commit(self, message):
        self.git('add', '.')
        self.git('commit', '-qm', message)
        return self.git('rev-parse', 'HEAD')

    def plan(self, math=True):
        self.write('Aglib/Base.lean' if math else 'README.md',
                   'module\ndef x := 2\n' if math else 'Documentation only.\n')
        head = self.commit('current committed change')
        return core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)

    def source(self, commands=None):
        return core.run_phase(self.root, self.state, 'source', executor=commands or Commands(self.root))

    def native(self, commands=None):
        return core.run_phase(self.root, self.state, 'native', self.progress,
                              commands or Commands(self.root), TOOLCHAIN)

    def finalize(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return core.finalize(self.root, self.state, Path(self.temp.name) / 'outputs.jsonl', TOOLCHAIN)

    def test_docs_only_finalization_inherits_exact_math_and_never_runs_native(self):
        plan = self.plan(math=False)
        self.assertFalse(plan['scope']['native'])
        commands = Commands(self.root)
        self.source(commands)
        result = self.finalize()
        self.assertEqual(result['status'], 'complete')
        self.assertEqual(result['required_phases'], ['source'])
        self.assertFalse(any('lake' in t['command'] for t in commands.calls))
        self.assertFalse((Path(self.temp.name) / 'outputs.jsonl').exists())

    def test_unbounded_native_policy_changes_fail_even_with_pending_math(self):
        original = {p: (self.root / p).read_text() for p in core.SEMANTIC_POLICY}
        for index, path in enumerate(core.SEMANTIC_POLICY):
            with self.subTest(policy=path):
                for other, text in original.items():
                    self.write(other, text)
                self.write(path, original[path] + '\n-- changed native predicate\n')
                if index % 2:
                    self.write('Aglib/Base.lean', 'module\ndef x := 3\n')
                head = self.commit('unbounded native check policy change')
                with self.assertRaisesRegex(ValueError, 'Native semantic policy changed'):
                    core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
                self.assertFalse((self.state / 'plan.json').exists())

    def test_executor_only_change_requires_native_controls(self):
        self.write('scripts/ci_pipeline.py', '# changed native executor\n')
        head = self.commit('executor integration change')
        plan = core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.assertTrue(plan['scope']['native'])
        self.assertTrue(plan['scope']['controls'])
        self.assertEqual(plan['required_phases'], ['source', 'native'])

    def test_fixed_ci_lean_source_requires_native_integration_without_math_scope(self):
        self.write('ci/fixtures/quartz/Check.lean', 'example : True := trivial\n')
        head = self.commit('fixed CI Lean fixture')
        plan = core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.assertEqual(plan['baseline_math'], plan['head_math'])
        self.assertEqual(plan['scope']['providers'] + plan['scope']['consumers'] + plan['scope']['tests'], [])
        self.assertTrue(plan['scope']['controls'] and plan['scope']['native'])
        self.assertEqual(plan['required_phases'], ['source', 'native'])
        required = core.tasks(self.root, plan, 'native', self.state / 'required-native')
        self.assertIn('core-native-cache', [task['id'] for task in required])

    def test_audit_uses_fixed_source_and_binds_its_actual_imports(self):
        plan = self.plan()
        audits = [task for task in core.tasks(self.root, plan, 'native', self.state / 'required-native')
                  if task.get('check_kind') == 'audit']
        self.assertTrue(audits)
        for task in audits:
            self.assertNotIn('generated', task)
            self.assertIn('--run', task['command'])
            self.assertIn(core.AUDIT_DRIVER, task['command'])
            self.assertEqual(json.loads(task['command'][-1]),
                             [name.split('.') for name in task['selection']])
            self.assertIn('Lean.Data.Json.Parser', core.reflection_roots(self.root, task))
        self.source()
        self.native()
        self.assertEqual(self.finalize()['status'], 'complete')

    def test_exact_generated_audit_predecessor_has_a_bounded_static_migration(self):
        old_pipeline = subprocess.check_output(
            ['git', 'show', 'f0ff076:scripts/ci_pipeline.py'], cwd=core.ROOT, text=True)
        for path in core.FIXED_AUDIT_SOURCES:
            (self.root / path).unlink()
        self.write('scripts/ci_pipeline.py', old_pipeline)
        anchor = self.commit('exact former audit generator')
        self.api.runs[0]['head_sha'] = anchor
        for path in core.FIXED_AUDIT_SOURCES:
            self.write(path, (core.ROOT / path).read_text())
        self.write('scripts/ci_pipeline.py', (core.ROOT / 'scripts/ci_pipeline.py').read_text())
        head = self.commit('fixed audit entrypoint')
        with patch.object(core.ci_baseline, 'REVIEWED_LEGACY_HEADS', frozenset({anchor})):
            plan = core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.assertEqual(plan['baseline_math'], plan['head_math'])
        self.assertEqual(plan['native_policy']['mode'], 'reviewed-fixed-audit-entrypoint-migration')
        self.assertEqual(plan['native_policy']['old_generator_blob'], core.OLD_AUDIT_GENERATOR_BLOB)
        self.assertEqual(plan['native_policy']['old_audit_source_blobs'], core.OLD_AUDIT_SOURCE_BLOBS)
        self.assertTrue(plan['scope']['native'] and plan['scope']['controls'])

    def test_other_predecessor_audit_sources_cannot_inherit_the_fixed_migration(self):
        old_pipeline = subprocess.check_output(
            ['git', 'show', 'f0ff076:scripts/ci_pipeline.py'], cwd=core.ROOT, text=True)
        reviewed = {path: (core.ROOT / path).read_text() for path in core.OLD_AUDIT_SOURCE_BLOBS}
        for index, path in enumerate(reviewed):
            with self.subTest(path=path):
                for fixed in core.FIXED_AUDIT_SOURCES:
                    (self.root / fixed).unlink()
                for source, text in reviewed.items():
                    self.write(source, text)
                changed = (reviewed[path].replace('hidden.size == 1', 'hidden.size ≤ 1')
                           if path == 'AglibTest/Axioms.lean' else
                           reviewed[path] + '\n-- Different previously adopted audit source.\n')
                self.assertNotEqual(changed, reviewed[path])
                self.write(path, changed)
                self.write('scripts/ci_pipeline.py', old_pipeline)
                anchor = self.commit('same generator with different predecessor audit source')
                self.api.runs[0]['head_sha'] = anchor
                for fixed in core.FIXED_AUDIT_SOURCES:
                    self.write(fixed, (core.ROOT / fixed).read_text())
                self.write('scripts/ci_pipeline.py', (core.ROOT / 'scripts/ci_pipeline.py').read_text())
                head = self.commit('fixed entrypoint after different predecessor audit source')
                self.assertEqual(self.git('show', anchor + ':' + path),
                                 self.git('show', head + ':' + path))
                state = self.state / str(index)
                with patch.object(core.ci_baseline, 'REVIEWED_LEGACY_HEADS', frozenset({anchor})), \
                        self.assertRaisesRegex(ValueError, 'Native semantic policy changed'):
                    core.create_plan(self.root, REPOSITORY, 'main', head, state, api=self.api)
                self.assertFalse((state / 'plan.json').exists())

    def test_unknown_generator_cannot_inherit_the_fixed_audit_migration(self):
        for path in core.FIXED_AUDIT_SOURCES:
            (self.root / path).unlink()
        self.write('scripts/ci_pipeline.py', '# unreviewed audit generator\n')
        anchor = self.commit('unknown audit generator')
        self.api.runs[0]['head_sha'] = anchor
        for path in core.FIXED_AUDIT_SOURCES:
            self.write(path, (core.ROOT / path).read_text())
        head = self.commit('fixed auditor after unknown policy')
        with patch.object(core.ci_baseline, 'REVIEWED_LEGACY_HEADS', frozenset({anchor})), \
                self.assertRaisesRegex(ValueError, 'Native semantic policy changed'):
            core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.assertFalse((self.state / 'plan.json').exists())

    def test_core_integration_failure_prevents_completion_with_unchanged_math(self):
        self.write('scripts/ci_pipeline.py', '# changed native executor\n')
        head = self.commit('core integration change')
        core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.source()
        commands = Commands(self.root, fail='core-native-cache')
        with self.assertRaisesRegex(ValueError, 'core-native-cache'):
            self.native(commands)
        with self.assertRaises(ValueError):
            self.finalize()
        self.assertFalse((self.state / 'complete.json').exists())

    def test_workflow_only_change_requires_native_cache_integration_and_completion(self):
        self.write('.github/workflows/ci.yml', FULL + '\n# workflow integration change\n')
        head = self.commit('workflow-only integration change')
        plan = core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.assertEqual(plan['baseline_math'], plan['head_math'])
        self.assertTrue(plan['scope']['native'] and plan['scope']['controls'])
        self.assertEqual(plan['required_phases'], ['source', 'native'])
        required = core.tasks(self.root, plan, 'native', self.state / 'required-native')
        self.assertIn('core-native-cache', [task['id'] for task in required])
        self.source()
        commands = Commands(self.root, fail='core-native-cache')
        with self.assertRaisesRegex(ValueError, 'core-native-cache'):
            self.native(commands)
        with self.assertRaises(ValueError):
            self.finalize()
        self.assertFalse((self.state / 'complete.json').exists())

    def test_dependency_pin_update_assigns_current_checks_and_prepared_client(self):
        manifest = json.loads((self.root / 'lake-manifest.json').read_text())
        manifest['packages'] = [{'name': 'upstream', 'rev': 'new-revision', 'inherited': False}]
        self.write('lake-manifest.json', json.dumps(manifest))
        prepare_downstream.prepare(self.root)
        head = self.commit('upstream dependency transition')
        plan = core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        scope = plan['scope']
        self.assertTrue(scope['configuration_update'])
        self.assertTrue(scope['controls'] and scope['client_audit'])
        self.assertIn('Aglib.Cold', scope['providers'])
        self.assertIn('AglibTest.Positive', scope['tests'])
        self.assertIn('Consumer.Use', scope['client'])
        self.assertEqual(plan['native_policy']['mode'], 'fresh-current-checks-after-configuration-update')
        self.source()
        self.native()
        self.assertEqual(self.finalize()['status'], 'complete')

    def test_stale_tracked_client_manifest_rejects_before_native_work(self):
        manifest = json.loads((self.root / 'lake-manifest.json').read_text())
        manifest['packages'] = [{'name': 'upstream', 'rev': 'new-revision', 'inherited': False}]
        self.write('lake-manifest.json', json.dumps(manifest))
        head = self.commit('unprepared upstream update')
        with self.assertRaisesRegex(ValueError, 'Tracked downstream manifest is stale'):
            core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.assertFalse((self.state / 'plan.json').exists())

    def test_toolchain_update_cannot_become_empty_native_scope(self):
        self.write('lean-toolchain', 'new-toolchain\n')
        head = self.commit('compiler transition')
        plan = core.create_plan(self.root, REPOSITORY, 'main', head, self.state, api=self.api)
        self.assertTrue(plan['scope']['configuration_update'])
        self.assertEqual(plan['required_phases'], ['source', 'native'])
        scope = json.loads(json.dumps(plan['scope']))
        scope['providers'].remove('Aglib.Cold')
        with self.assertRaisesRegex(ValueError, 'complete current check scope'):
            core.assert_native_scope(self.root, scope, plan['baseline_math'], plan['head_math'], scope['changed'])

    def _runtime_mutation(self, restored):
        self.plan()
        self.source()
        prefix = Path(self.temp.name) / 'compiler'
        (prefix / 'bin').mkdir(parents=True)
        (prefix / 'lib/lean').mkdir(parents=True)
        for path in ('bin/lean', 'bin/lake', 'lib/lean/libleanshared.so'):
            (prefix / path).write_bytes(b'original runtime')
        shared = prefix / 'lib/lean/libleanshared.so'
        original_check_output = subprocess.check_output
        def locate(command, *args, **kwargs):
            if command[:2] == ['elan', 'which']:
                return str(prefix / 'bin' / command[-1]) + '\n'
            return original_check_output(command, *args, **kwargs)
        commands = Commands(self.root)
        run = commands.run
        def mutate(task, directory):
            value = run(task, directory)
            if task['kind'] == 'check':
                shared.write_bytes(b'incompatible runtime')
                if restored:
                    shared.write_bytes(b'original runtime')
            return value
        commands.run = mutate
        with patch('ci_pipeline.subprocess.check_output', side_effect=locate):
            with self.assertRaises(InputDrift):
                core.run_phase(self.root, self.state, 'native', self.progress, commands)
        self.assertEqual(list(self.progress.glob('*.json')), [])
        self.assertNotEqual(read_json(self.state / 'native.json')['status'], 'completed')

    def test_changed_runtime_cannot_save_check_before_phase_failure(self):
        self._runtime_mutation(False)

    def test_restored_runtime_cannot_save_check_before_phase_failure(self):
        self._runtime_mutation(True)

    def test_native_client_setup_precedes_reflective_checks_and_keeps_tracked_bytes(self):
        plan = self.plan()
        manifest = self.root / core.GENERATED_MANIFEST
        self.assertIn(core.GENERATED_MANIFEST, plan['source_files'])
        stamp = core.ReflectionGraph.stamp(manifest)
        self.source()
        commands = Commands(self.root)
        self.native(commands)
        ids = [t['id'] for t in commands.calls]
        self.assertLess(ids.index('prepare-client'), ids.index('reflection-environment'))
        self.assertEqual(core.ReflectionGraph.stamp(manifest), stamp)

    def test_real_pending_math_cannot_finalize_after_only_source_or_empty_native_record(self):
        self.plan()
        self.source()
        with self.assertRaises(OSError):
            self.finalize()
        write_json(self.state / 'native.json', {'status': 'completed', 'tasks': []})
        with self.assertRaisesRegex(ValueError, 'wrong-plan'):
            self.finalize()
        self.assertFalse((self.state / 'complete.json').exists())

    def test_empty_scope_bug_is_rejected_independently_of_selector(self):
        original = core.affected_scope.select
        def broken(*args, **kwargs):
            scope = original(*args, **kwargs)
            scope.update(native=False, providers=[], consumers=[], tests=[], trust=False,
                         client=[], client_audit=False, controls=False)
            return scope
        with patch.object(core.affected_scope, 'select', side_effect=broken):
            with self.assertRaisesRegex(ValueError, 'Changed mathematical'):
                self.plan()

    def test_native_success_requires_all_tasks_and_one_shared_root_build(self):
        plan = self.plan()
        self.source()
        commands = Commands(self.root)
        self.native(commands)
        result = self.finalize()
        self.assertEqual(result['status'], 'complete')
        self.assertTrue(result['native_root_graph'])
        self.assertTrue(result['client_graph'])
        graph = [t for t in commands.calls if t['id'] == 'shared-root-build']
        self.assertEqual(len(graph), 1)
        self.assertEqual(graph[0]['command'][:3], ['lake', '--rehash', 'build'])
        preflight = next(t for t in commands.calls if t['id'] == 'unrelated-cached-imports')
        self.assertIn('Aglib.Cold', preflight['command'])
        self.assertNotIn('Aglib.Base', preflight['command'])
        builtin = [t for t in commands.calls if t.get('check_kind') == 'builtin']
        self.assertTrue(builtin)
        self.assertTrue(all('--rehash' not in t['command'] for t in builtin))
        self.assertEqual(commands.calls[-1]['id'], 'root-graph')
        self.assertEqual(commands.calls[-1]['command'][:4], ['lake', '--rehash', '--no-build', 'build'])
        self.assertEqual(result['baseline']['run_id'], 12)

    def test_late_failure_keeps_successes_then_reuses_checks_with_full_import_binding(self):
        self.plan()
        self.source()
        failed = Commands(self.root, fail='consumers/declaration/0')
        with self.assertRaisesRegex(ValueError, 'Actual command failed'):
            self.native(failed)
        self.assertTrue(list(self.progress.glob('*.json')))
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            self.finalize()
        again = Commands(self.root)
        self.native(again)
        result = self.finalize()
        self.assertIn('providers/builtin/0', result['reused_checks'])
        self.assertIn('providers/declaration/0', result['reused_checks'])
        self.assertIn('shared-root-build', [t['id'] for t in again.calls])
        self.assertNotIn('providers/builtin/0', [t['id'] for t in again.calls])

    def test_cold_unrelated_gap_stops_before_any_build(self):
        self.plan()
        self.source()
        commands = Commands(self.root, fail='unrelated-cached-imports')
        with self.assertRaises(ValueError):
            self.native(commands)
        self.assertEqual([t['id'] for t in commands.calls], ['prepare-client', 'unrelated-cached-imports'])

    def test_zero_exit_empty_adapter_does_not_cover_required_work(self):
        self.plan()
        with self.assertRaisesRegex(ValueError, 'Missing successful resource receipt'):
            self.source(Commands(self.root, empty='generate_imports.py'))
        with self.assertRaises(ValueError):
            self.finalize()

    def test_wrong_plan_omitted_task_and_forged_boolean_completions_are_rejected(self):
        self.plan(math=False)
        self.source()
        original = read_json(self.state / 'source.json')
        for change in ('wrong-plan', 'omitted-task', 'forged-boolean'):
            value = json.loads(json.dumps(original))
            if change == 'wrong-plan':
                value['plan_id'] = 'other plan'
            elif change == 'omitted-task':
                value['tasks'].pop()
            else:
                value['tasks'][0]['result'] = {'success': True, 'exit_code': 0}
            write_json(self.state / 'source.json', value)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.finalize()

    def test_source_drift_and_native_output_corruption_prevent_finalization(self):
        self.plan()
        self.source()
        self.native()
        output = self.root / '.lake/build/lib/lean/Aglib/Cold.olean'
        output.write_bytes(b'corrupt unrelated output after final barrier')
        with self.assertRaisesRegex(ValueError, 'graph outputs drifted'):
            self.finalize()
        self.write('Aglib/Base.lean', 'module\ndef x := 3\n')
        with self.assertRaisesRegex(ValueError, 'working-tree changes'):
            self.finalize()

    def test_failed_retry_retracts_previous_completion_artifacts(self):
        self.plan(math=False)
        self.source()
        self.finalize()
        self.assertTrue((self.state / 'complete.json').exists())
        with self.assertRaises(ValueError):
            self.source(Commands(self.root, fail='generate_imports.py'))
        self.assertFalse((self.state / 'complete.json').exists())
        outputs = Path(self.temp.name) / 'outputs.jsonl'
        outputs.write_text('stale mapping')
        outputs.with_suffix('.jsonl.coverage.json').write_text('stale complete coverage')
        with self.assertRaises(ValueError):
            self.finalize()
        self.assertFalse(outputs.exists())
        self.assertFalse(outputs.with_suffix('.jsonl.coverage.json').exists())


if __name__ == '__main__':
    unittest.main()
