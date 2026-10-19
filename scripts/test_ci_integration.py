"""Exercise CI acceptance against real Git histories without running Lean."""
import json
from contextlib import redirect_stdout
import io
from pathlib import Path
import subprocess
import tempfile
import unittest

import ci_pipeline
from ci_state import digest


REPOSITORY = 'fixture/aglib'
LEGACY_WORKFLOW = '''jobs:
  library:
    steps:
      - name: Run CI checks for the library and independent client
        run: bash scripts/check.sh --rehash --ci
'''
UNSAFE_WORKFLOW = '''jobs:
  library:
    steps:
      - run: python3 scripts/affected_scope.py --base "$PREVIOUS_PUSH"
'''


class HistoryAPI:
    def __init__(self, verified, later=None):
        self.verified, self.later = verified, later

    def get(self, path, **query):
        if path == '':
            return {'full_name': REPOSITORY, 'default_branch': 'main'}
        raise AssertionError(path)

    def pages(self, path, key, **query):
        if key == 'workflow_runs':
            revisions = ([self.later] if self.later else []) + [self.verified]
            for index, revision in enumerate(revisions):
                yield {'id': index + 100, 'run_attempt': 1, 'head_sha': revision,
                       'head_branch': 'main', 'status': 'completed', 'conclusion': 'success',
                       'event': 'push', 'path': '.github/workflows/ci.yml',
                       'head_repository': {'full_name': REPOSITORY},
                       'html_url': f'https://github.com/{REPOSITORY}/actions/runs/{index + 100}'}
        elif key == 'jobs':
            yield {'name': 'library', 'status': 'completed', 'conclusion': 'success',
                   'steps': [{'name': 'Run CI checks for the library and independent client',
                              'status': 'completed', 'conclusion': 'success'}]}
        else:
            raise AssertionError((path, key, query))


class SourceExecutor:
    def run(self, task, directory):
        if task['kind'] not in {'source', 'process'}:
            raise AssertionError('The source phase attempted native work: ' + task['kind'])
        return {'receipt': {'state': 'completed', 'command': task['command'],
                            'cwd': task['cwd'], 'exit_code': 0,
                            'guard_failure': None, 'owned_group_gone': True}}


class CIIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='aglib-ci-integration-')
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.root = self.directory / 'checkout'
        self.root.mkdir()
        self.git('init', '-qb', 'main')
        self.write('.gitignore', '.lake/\n__pycache__/\n')
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lakefile.toml', 'name = "Aglib"\n')
        self.write('lake-manifest.json', '{"packages": []}\n')
        self.write('Aglib/Base.lean', 'module\ndef value : Nat := 1\n')
        self.write('Aglib.lean', 'module\npublic import Aglib.Base\n')
        self.write('AglibTest/Use.lean', 'import Aglib.Base\nexample : True := trivial\n')
        self.write('AglibTest.lean', 'import AglibTest.Use\n')
        self.write('AglibTest/AuditSupport.lean', 'import Lean\ndef support := 1\n')
        self.write('AglibTest/AuditCoverage.lean', 'module\ndef coverage := 1\n')
        self.write('README.md', 'CI integration fixture.\n')
        self.write('.github/workflows/ci.yml', LEGACY_WORKFLOW)
        self.base = self.commit('verified native baseline')

    def git(self, *arguments):
        return subprocess.check_output(['git', *arguments], cwd=self.root, text=True).strip()

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def commit(self, message):
        self.git('add', '.')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', message)
        return self.git('rev-parse', 'HEAD')

    def history_with_unchecked_proof(self):
        self.write('Aglib/Base.lean', 'module\ndef value : Nat := 2\n')
        self.write('.github/workflows/ci.yml', UNSAFE_WORKFLOW)
        self.unverified = self.commit('proof whose CI did not finish')
        self.write('scripts/cache_ci.py', '# later cache-script repair\n')
        self.head = self.commit('source-only green after failed proof CI')
        return HistoryAPI(self.base, self.head)

    def plan(self, api, name='state', requested_base=None):
        state = self.directory / name
        plan = ci_pipeline.create_plan(self.root, REPOSITORY, 'main',
                                       self.git('rev-parse', 'HEAD'), state,
                                       requested_base=requested_base, api=api)
        return state, plan

    def source(self, state, executor=None):
        return ci_pipeline.run_phase(self.root, state, 'source',
                                     executor=executor or SourceExecutor())

    def assert_incomplete(self, state):
        with self.assertRaises((ValueError, OSError)):
            ci_pipeline.finalize(self.root, state, toolchain={'fixture': 'no Lean invoked'})
        self.assertFalse((state / 'complete.json').exists())

    def test_failed_proof_remains_required_after_source_only_green(self):
        state, plan = self.plan(self.history_with_unchecked_proof())
        self.assertEqual(plan['scope']['base'], self.base)
        self.assertIn('Aglib.Base', plan['scope']['providers'])
        self.assertEqual(plan['required_phases'], ['source', 'native'])
        self.source(state)
        self.assert_incomplete(state)

    def test_handwritten_native_success_does_not_supply_missing_checks(self):
        state, plan = self.plan(self.history_with_unchecked_proof())
        self.source(state)
        (state / 'native.json').write_text(json.dumps(
            {'schema': 1, 'plan_id': plan['id'], 'phase': 'native',
             'status': 'completed', 'tasks': []}))
        self.assert_incomplete(state)

    def test_source_only_inherits_only_unchanged_mathematical_snapshot(self):
        self.write('README.md', 'Changed documentation; mathematical inputs unchanged.\n')
        self.commit('documentation')
        state, plan = self.plan(HistoryAPI(self.base))
        self.assertEqual(plan['required_phases'], ['source'])
        self.source(state)
        with redirect_stdout(io.StringIO()):
            result = ci_pipeline.finalize(self.root, state)
        self.assertEqual(result['status'], 'complete')
        self.assertEqual(result['coverage'], 'inherited-unchanged-mathematical-snapshot')

    def test_source_drift_after_source_phase_prevents_completion(self):
        self.write('README.md', 'Documentation edit.\n')
        self.commit('documentation')
        state, _ = self.plan(HistoryAPI(self.base))
        self.source(state)
        self.write('Aglib/Base.lean', 'module\ndef value : Nat := 3\n')
        self.assert_incomplete(state)

    def test_phase_record_from_another_invocation_cannot_complete_this_one(self):
        self.write('README.md', 'Documentation edit.\n')
        self.commit('documentation')
        first, _ = self.plan(HistoryAPI(self.base), 'first')
        second, _ = self.plan(HistoryAPI(self.base), 'second')
        self.source(first)
        (second / 'source.json').write_bytes((first / 'source.json').read_bytes())
        self.assert_incomplete(second)

    def test_manual_base_cannot_skip_an_unchecked_proof_commit(self):
        api = self.history_with_unchecked_proof()
        with self.assertRaisesRegex(ValueError, 'verified base|ancestor'):
            self.plan(api, requested_base=self.unverified)

    def test_rehashing_a_tampered_plan_cannot_erase_native_requirements(self):
        state, plan = self.plan(self.history_with_unchecked_proof())
        plan['scope']['native'] = False
        plan['required_phases'] = ['source']
        plan['id'] = digest({key: value for key, value in plan.items() if key != 'id'})
        (state / 'plan.json').write_text(json.dumps(plan))
        with self.assertRaisesRegex(ValueError, 'scope|mathematical|requirements'):
            self.source(state)
        self.assertFalse((state / 'complete.json').exists())

    def test_exit_zero_without_a_complete_receipt_cannot_cover_source_checks(self):
        class ExitOnly:
            def run(self, task, directory):
                return {'receipt': {'exit_code': 0}}
        self.write('README.md', 'Documentation edit.\n')
        self.commit('documentation')
        state, _ = self.plan(HistoryAPI(self.base))
        with self.assertRaises(ValueError):
            self.source(state, ExitOnly())
        self.assert_incomplete(state)


if __name__ == '__main__':
    unittest.main()
