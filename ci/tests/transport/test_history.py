"""Hosted baseline evidence: pinned common producer and exact native attempt."""
import copy
import hashlib
import base64
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.transport import history
from lean_ci.transport.github import APIUnavailable, BaselineError

CORE = 'a' * 40
RELEASE = 'b' * 40
REPOSITORY = 'kangxyz/aglib'
# Synthetic producer template keeps core fixtures independent of adoption B.
TEMPLATE = b'name: common fixture\njobs:\n  native:\n    steps:\n      - with:\n          ref: PENDING_COMMON_CORE_REVISION\n'


class API:
    def __init__(self, repository=REPOSITORY):
        self.repository = repository
        self.runs = []
        self.details = {}
        self.jobs = {}
        self.sources = {}
        self.errors = {}
        self.calls = []

    def get(self, path, **query):
        self.calls.append((path, query))
        if path in self.errors:
            raise self.errors[path]
        if path == '':
            return {'full_name': self.repository, 'default_branch': 'main'}
        if path.startswith('/contents/'):
            content = self.sources[(path.removeprefix('/contents/'), query['ref'])]
            return {'type': 'file', 'encoding': 'base64',
                    'content': base64.b64encode(content).decode()}
        return copy.deepcopy(self.details[path])

    def pages(self, path, key, **query):
        self.calls.append((path, query))
        if path in self.errors:
            raise self.errors[path]
        if path == '/actions/runs':
            return iter(copy.deepcopy(self.runs))
        return iter(copy.deepcopy(self.jobs[path]))


class HistoryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.git('init', '-q')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.git('config', 'user.name', 'History fixture')
        self.write('README', 'root\n')
        self.first = self.save('root')
        self.workflow = TEMPLATE.replace(b'PENDING_COMMON_CORE_REVISION', CORE.encode())
        self.write('.github/workflows/lean-ci.yml', self.workflow)
        self.write('.github/workflows/ci.yml', 'name: fixture\non: push\njobs:\n  ci:\n    uses: ./.github/workflows/lean-ci.yml\n')
        self.write('.github/lean-ci.toml', 'schema = 1\n')
        self.baseline = self.save('common adoption')
        self.write('README', 'next\n')
        self.head = self.save('next source')
        self.api = API()
        self.run = {'id': 5, 'run_attempt': 2, 'status': 'completed', 'conclusion': 'success',
                    'head_branch': 'main', 'event': 'push', 'head_sha': self.baseline,
                    'path': '.github/workflows/ci.yml',
                    'head_repository': {'full_name': REPOSITORY},
                    'repository': {'full_name': REPOSITORY},
                    'referenced_workflows': [{'path': REPOSITORY + '/' + history.WORKFLOW + '@refs/heads/main',
                                               'sha': self.baseline}]}
        self.job = {'name': 'ci / native', 'status': 'completed', 'conclusion': 'success',
                    'run_id': 5, 'run_attempt': 2,
                    'steps': [{'name': name, 'status': 'completed', 'conclusion': 'success'}
                              for name in (history.NATIVE_STEP, history.FINALIZE_STEP)]}
        self.install()
        self.addCleanup(patch.stopall)
        patch.object(history, 'core_revision', return_value=CORE).start()
        patch.object(history, 'COMMON_TEMPLATE_SHA256', hashlib.sha256(TEMPLATE).hexdigest()).start()
        patch.dict(os.environ, {'GITHUB_RUN_ID': '999999'}).start()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def write(self, path, content):
        path = self.root / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content if isinstance(content, bytes) else content.encode())

    def save(self, message):
        self.git('add', '.')
        self.git('commit', '-qm', message)
        return self.git('rev-parse', 'HEAD')

    def install(self):
        self.api.runs = [copy.deepcopy(self.run)]
        self.api.details['/actions/runs/5'] = copy.deepcopy(self.run)
        self.api.jobs['/actions/runs/5/attempts/2/jobs'] = [copy.deepcopy(self.job)]

    def select(self, **arguments):
        return history.select_baseline(self.root, self.api.repository, 'main', self.head,
                                       api=self.api, **arguments)

    def assert_initial(self):
        result = self.select()
        self.assertEqual(result['kind'], 'initial')
        self.assertEqual(result['head'], self.head)
        self.assertNotIn('base', result)
        self.assertNotIn('verified_base', result)

    def test_exact_native_attempt_is_accepted(self):
        result = self.select()
        self.assertEqual(result['kind'], 'verified')
        self.assertEqual(result['base'], self.baseline)
        self.assertEqual(result['verified_base'], self.baseline)
        self.assertEqual(result['run_attempt'], 2)
        self.assertEqual(result['common_core'], CORE)
        self.assertEqual(result['job_evidence']['attempt_bound_by'], 'exact-attempt endpoint')

    def test_true_absence_initializes_without_inventing_base(self):
        self.api.runs = []
        self.assert_initial()

    def test_old_green_caller_is_not_common_evidence(self):
        self.git('checkout', '-q', self.first)
        self.write('.github/workflows/ci.yml', 'jobs:\n  library:\n    runs-on: ubuntu-latest\n')
        self.run['head_sha'] = self.save('legacy green')
        self.head = self.run['head_sha']
        self.install()
        self.assert_initial()

    def test_source_only_or_incomplete_native_never_verifies(self):
        for change in ('native skipped', 'finalize missing', 'native failure', 'job skipped'):
            with self.subTest(change=change):
                self.install()
                job = self.api.jobs['/actions/runs/5/attempts/2/jobs'][0]
                if change == 'native skipped':
                    job['steps'][0]['conclusion'] = 'skipped'
                elif change == 'finalize missing':
                    job['steps'].pop()
                elif change == 'native failure':
                    job['steps'][0]['conclusion'] = 'failure'
                else:
                    job['conclusion'] = 'skipped'
                self.assert_initial()

    def test_fork_and_pull_request_runs_never_verify(self):
        original = copy.deepcopy(self.run)
        for field, value in [('head_repository', {'full_name': 'fork/aglib'}),
                             ('repository', {'full_name': 'fork/aglib'}),
                             ('event', 'pull_request'), ('head_branch', 'feature')]:
            with self.subTest(field=field):
                self.run = dict(original, **{field: value})
                self.install()
                self.assert_initial()

    def test_exact_source_ancestry_required(self):
        self.git('checkout', '-q', self.first)
        self.write('README', 'side branch\n')
        self.head = self.save('unrelated side source')
        self.assert_initial()

    def test_same_name_fake_workflow_is_rejected(self):
        self.git('checkout', '-q', self.baseline)
        self.write('.github/workflows/lean-ci.yml', self.workflow + b'\n# changed producer\n')
        self.run['head_sha'] = self.save('altered producer')
        self.head = self.run['head_sha']
        self.run['referenced_workflows'][0]['sha'] = self.head
        self.install()
        self.assert_initial()

    def test_reference_and_release_core_must_match(self):
        for field, value in [('sha', 'c' * 40), ('path', 'other/aglib/' + history.WORKFLOW + '@main')]:
            with self.subTest(field=field):
                self.install()
                self.api.details['/actions/runs/5']['referenced_workflows'][0][field] = value
                self.assert_initial()
        with patch.object(history, 'core_revision', return_value='d' * 40):
            self.install()
            self.assert_initial()

    def test_attempt_cannot_be_inherited_from_another_attempt(self):
        self.api.details['/actions/runs/5']['run_attempt'] = 3
        self.assert_initial()
        self.install()
        self.api.jobs['/actions/runs/5/attempts/2/jobs'][0]['run_attempt'] = 1
        self.assert_initial()

    def test_fallback_jobs_require_explicit_attempt_coordinates(self):
        path = '/actions/runs/5/attempts/2/jobs'
        self.api.errors[path] = APIUnavailable('attempt endpoint unavailable')
        self.api.jobs['/actions/runs/5/jobs'] = [copy.deepcopy(self.job)]
        self.assertEqual(self.select()['kind'], 'verified')
        del self.api.jobs['/actions/runs/5/jobs'][0]['run_attempt']
        self.assert_initial()

    def test_api_outage_propagates_instead_of_initializing(self):
        for path in ('', '/actions/runs', '/actions/runs/5', '/actions/runs/5/attempts/2/jobs'):
            with self.subTest(path=path):
                self.api.errors = {path: APIUnavailable('offline')}
                if path.endswith('/jobs'):
                    self.api.errors['/actions/runs/5/jobs'] = APIUnavailable('also offline')
                with self.assertRaises(APIUnavailable):
                    self.select()

    def test_requested_base_only_widens_an_accepted_base(self):
        self.assertEqual(self.select(requested_base=self.first)['base'], self.first)
        with self.assertRaisesRegex(BaselineError, 'ancestor'):
            self.select(requested_base=self.head)
        self.api.runs = []
        with self.assertRaisesRegex(BaselineError, 'absent'):
            self.select(requested_base=self.first)

    def test_external_caller_resolves_pinned_producer_source(self):
        self.git('checkout', '-q', self.head)
        self.write('.github/workflows/ci.yml', 'name: fixture\non: push\njobs:\n  ci:\n    uses: kangxyz/aglib/.github/workflows/lean-ci.yml@' + RELEASE + '\n')
        self.head = self.save('external caller')
        self.run['head_sha'] = self.head
        self.api.repository = 'owner/consumer'
        for field in ('repository', 'head_repository'):
            self.run[field] = {'full_name': self.api.repository}
        self.run['referenced_workflows'] = [{'path': REPOSITORY + '/' + history.WORKFLOW + '@' + RELEASE,
                                            'sha': RELEASE}]
        self.install()
        producer = API()
        producer.sources[(history.WORKFLOW, RELEASE)] = self.workflow
        with patch.object(history, 'GitHubAPI', return_value=producer):
            self.assertEqual(self.select()['common_release'], RELEASE)
            producer.errors['/contents/' + history.WORKFLOW] = APIUnavailable('source offline')
            with self.assertRaises(APIUnavailable):
                self.select()

    def test_template_identity_is_current_before_release_substitution(self):
        self.assertTrue(history._workflow(self.workflow, CORE))
        self.assertFalse(history._workflow(self.workflow, '0' * 40))
        self.assertFalse(history._workflow(self.workflow + b'\n', CORE))




class WorkflowBridgeTests(unittest.TestCase):
    """Exercise only the portable relocation; no Actions cache/API is invoked."""
    def setUp(self):
        import textwrap
        path = next((parent / '.github/workflows/lean-ci.yml' for parent in Path(__file__).resolve().parents
                     if (parent / '.github/workflows/lean-ci.yml').is_file()), None)
        if path is None:
            self.skipTest('Adoption workflow is intentionally absent from tooling-core commit A')
        self.workflow = path.read_text()
        block = self.workflow.split('      - name: Adopt restored legacy cache directories\n', 1)[1].split('\n      - ', 1)[0]
        run = textwrap.dedent(block.split('        run: |\n', 1)[1])
        self.script = run.split("python3 -P - <<'PY'\n", 1)[1].rsplit('\nPY', 1)[0]
        self.temporary = tempfile.TemporaryDirectory(prefix='legacy-cache-fixture-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / 'source').mkdir()
        (self.root / 'tooling').mkdir()

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def adopt(self, dependencies='', builds=''):
        import sys
        environment = dict(os.environ, GITHUB_WORKSPACE=str(self.root),
                           LEGACY_DEPENDENCY_PATHS=dependencies, LEGACY_BUILD_PATHS=builds)
        return subprocess.run([sys.executable, '-P', '-'], input=self.script,
                              env=environment, text=True, capture_output=True)

    def test_original_root_dependency_client_and_upstream_outputs_survive_relocation(self):
        self.write('.lake/packages/Aglib/source.lean', 'dependency source')
        self.write('.lake/build/lib/lean/Project.olean', 'project cached output')
        self.write('examples/downstream/.lake/build/lib/lean/Consumer.olean', 'client cached output')
        self.write('source/.lake/build/lib/lean/Untouched.olean', 'existing compatible output')
        self.write('source/keep.txt', 'caller source')
        self.write('tooling/keep.txt', 'pinned core')
        result = self.adopt('.lake/packages', '.lake/build\nexamples/downstream/.lake/build')
        self.assertEqual(result.returncode, 0, result.stderr)
        for name, content in [('source/.lake/packages/Aglib/source.lean', 'dependency source'),
                              ('source/.lake/build/lib/lean/Project.olean', 'project cached output'),
                              ('source/examples/downstream/.lake/build/lib/lean/Consumer.olean', 'client cached output'),
                              ('source/.lake/build/lib/lean/Untouched.olean', 'existing compatible output'),
                              ('source/keep.txt', 'caller source'), ('tooling/keep.txt', 'pinned core')]:
            self.assertEqual((self.root / name).read_text(), content)
        self.assertFalse((self.root / '.lake/packages').exists())

    def test_nested_r5_cache_coordinates_preserve_relative_package_layout(self):
        self.write('lean/.lake/packages/pinned/source.lean', 'dependency')
        self.write('lean/.lake/build/lib/lean/R5Lab.olean', 'cached R5 output')
        result = self.adopt('lean/.lake/packages', 'lean/.lake/build')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.root / 'source/lean/.lake/build/lib/lean/R5Lab.olean').read_text(), 'cached R5 output')

    def test_quillen_project_cache_merges_upstream_outputs_into_restored_dependencies(self):
        self.write('source/.lake/packages/Aglib/.lake/build/lib/lean/Old.olean', 'retained peer')
        self.write('.lake/packages/Aglib/.lake/build/lib/lean/New.olean', 'recent upstream output')
        result = self.adopt(builds='.lake/packages/Aglib/.lake/build')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((self.root / 'source/.lake/packages/Aglib/.lake/build/lib/lean/Old.olean').is_file())
        self.assertTrue((self.root / 'source/.lake/packages/Aglib/.lake/build/lib/lean/New.olean').is_file())

    def test_escape_or_redirected_cache_coordinate_is_rejected(self):
        for value in ('../outside/.lake/build', '/tmp/.lake/build', 'source/.lake/build', 'tooling/.lake/packages'):
            with self.subTest(value=value):
                self.assertNotEqual(self.adopt(builds=value).returncode, 0)
        self.write('tooling/bad/marker', 'preserved')
        (self.root / '.lake').mkdir()
        (self.root / '.lake/packages').symlink_to(self.root / 'tooling/bad', target_is_directory=True)
        self.assertNotEqual(self.adopt(dependencies='.lake/packages').returncode, 0)
        self.assertEqual((self.root / 'tooling/bad/marker').read_text(), 'preserved')

    def test_cached_internal_symlink_cannot_escape_the_adopted_source_checkout(self):
        self.write('.lake/build/peer', 'cached peer')
        (self.root / '.lake/build/redirect').symlink_to('/tmp/outside-native-cache')
        self.assertNotEqual(self.adopt(builds='.lake/build').returncode, 0)
        self.assertTrue((self.root / '.lake/build/peer').is_file())

    def test_initial_adoption_event_selects_parent_core_but_ordinary_math_push_skips(self):
        import json
        import sys
        import textwrap
        source = self.root / 'source'
        def git(*args):
            return subprocess.check_output(['git', *args], cwd=source, text=True).strip()
        git('init', '-q'); git('config', 'user.name', 'workflow fixture'); git('config', 'user.email', 'fixture@example.invalid')
        self.write('source/ci/src/lean_ci/tool.py', '# old implementation\n')
        git('add', '.'); git('commit', '-qm', 'previous published source')
        before = git('rev-parse', 'HEAD')
        self.write('source/ci/src/lean_ci/tool.py', '# common implementation core A\n')
        git('add', '.'); git('commit', '-qm', 'core A')
        self.write('source/.github/workflows/lean-ci.yml', '# adoption workflow B\n')
        git('add', '.'); git('commit', '-qm', 'adoption B')
        adoption = git('rev-parse', 'HEAD')
        run = self.workflow.split('      - name: Select changed common tooling fixtures\n', 1)[1].split('      - name: Check changed common tooling fixtures\n', 1)[0]
        script = textwrap.dedent(run.split('        run: |\n', 1)[1]).split("python3 -P - <<'PY'\n", 1)[1].rsplit('\nPY', 1)[0]
        self.write('temp/source-state/plan.json', json.dumps({'scope': {'initial': True, 'base': None, 'changed': ['Tiny/Base.lean', '.github/lean-ci.toml']}}))
        environment = dict(os.environ, RUNNER_TEMP=str(self.root / 'temp'), GITHUB_WORKSPACE=str(self.root),
                           GITHUB_EVENT_PATH=str(self.root / 'event.json'), GITHUB_OUTPUT=str(self.root / 'output'))
        self.write('event.json', json.dumps({'before': before}))
        result = subprocess.run([sys.executable, '-P', '-'], input=script, cwd=source, env=environment, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.root / 'output').read_text(), 'python=true\nnative=true\n')
        self.write('source/Tiny/Base.lean', 'def base := 2\n')
        git('add', '.'); git('commit', '-qm', 'ordinary mathematical change')
        self.write('event.json', json.dumps({'before': adoption}))
        (self.root / 'output').unlink()
        result = subprocess.run([sys.executable, '-P', '-'], input=script, cwd=source, env=environment, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.root / 'output').read_text(), 'python=false\nnative=false\n')

    def test_finalize_and_candidate_native_fixture_have_concrete_workflow_gates(self):
        block = self.workflow.split('      - name: Finalize canonical coverage', 1)[1]
        self.assertIn('--github-output "$GITHUB_OUTPUT"', block)
        self.assertIn("steps.finalize.outputs.mappings == 'true'", block)
        self.assertNotIn('steps.plan.outputs.publish', self.workflow)
        self.assertIn("needs.source.outputs.candidate-native-fixtures == 'true'", self.workflow)
        self.assertIn('LEAN_CI_NATIVE_TEST_ROOT: ${{ steps.layout.outputs.package }}', self.workflow)
        self.assertIn('Prepared candidate native fixtures must execute without skips', self.workflow)
        self.assertNotIn('python3 -m lean_ci', self.workflow)


if __name__ == '__main__':
    unittest.main()
