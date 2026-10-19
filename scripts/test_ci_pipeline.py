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
from ci_state import file_hash, locate_module, module_identity, read_json, write_json
from test_ci_baseline import FixtureAPI, FULL, REPOSITORY
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
        self.write('.gitignore', '.lake/\nexamples/downstream/.lake/\nexamples/downstream/lake-manifest.json\n')
        self.write('Aglib/Base.lean', 'module\ndef x := 1\n')
        for name in ('Init', 'Lean', 'Lake'):
            self.write(name + '.lean', 'module\n')
            native_fixture(self.root, name)
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
        self.write('lake-manifest.json', '{"packages": []}\n')
        self.write('README.md', 'Initial documentation.\n')
        self.write('.github/workflows/ci.yml', FULL)
        for path in core.POLICY:
            if path.startswith('scripts/'):
                self.write(path, '# fixed checker fixture\n')
        self.write(core.DRIVERS[0], 'import Batteries.Tactic.Lint\n')
        self.write(core.DRIVERS[1], 'import Cli.Basic\n')
        self.write('.lake/packages/batteries/Batteries/Tactic/Lint.lean', 'import Lean\n')
        self.write('.lake/packages/Cli/Cli/Basic.lean', 'import Lean\n')
        self.git('init', '-q')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.anchor = self.commit('whole-native anchor')
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
        self.assertEqual([t['id'] for t in commands.calls], ['unrelated-cached-imports'])

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
