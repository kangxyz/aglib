"""Git/API fixtures for verified baseline selection; no Lean or cache operations."""
import contextlib
import io
import json
import os
from pathlib import Path
import ssl
import subprocess
import tempfile
import unittest
import urllib.error
from unittest.mock import patch

from ci_baseline import (APIUnavailable, BaselineError, FINALIZE_STEP, GitHubAPI,
                         NATIVE_STEP, main, select, workflow_kind)


REPOSITORY = 'fixture/aglib'
FULL = '''name: Aglib CI
jobs:
  library:
    steps:
      - name: Run CI checks for the library and independent client
        run: |
          set -euo pipefail
          lean --version
          bash scripts/check.sh --rehash --ci
'''
UNSAFE = FULL.replace('bash scripts/check.sh --rehash --ci',
                      'python3 scripts/affected_scope.py --base "$BEFORE"\n'
                      '          bash scripts/check.sh --rehash --ci --native-only --plan plan.json')
SAFE = UNSAFE.replace('python3 scripts/affected_scope.py --base "$BEFORE"',
                      'python3 scripts/ci_pipeline.py plan --head "$GITHUB_SHA" \\\n'
                      '            --repository "$GITHUB_REPOSITORY" --state "$RUNNER_TEMP/state"\n'
                      '          python3 scripts/ci_pipeline.py source --state "$RUNNER_TEMP/state"\n'
                      '          python3 scripts/ci_pipeline.py native --state "$RUNNER_TEMP/state"\n'
                      '          python3 scripts/ci_pipeline.py finalize --state "$RUNNER_TEMP/state"')


class FixtureAPI(GitHubAPI):
    """Use the real pagination contract with fixed API responses."""
    def __init__(self, runs=(), jobs=None):
        self.runs = list(runs)
        self.jobs = jobs or {}
        self.metadata = {'full_name': REPOSITORY, 'default_branch': 'main'}
        self.calls = []

    def get(self, path, **query):
        self.calls.append((path, query))
        if not path:
            return self.metadata
        start = (query['page'] - 1) * query['per_page']
        if path == '/actions/workflows/ci.yml/runs':
            if query['branch'] != 'main' or query['status'] != 'success':
                raise AssertionError('Run query must select successful default-branch CI')
            return {'workflow_runs': self.runs[start:start + query['per_page']]}
        return {'jobs': self.jobs.get(path, [])[start:start + query['per_page']]}


class BaselineTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aglib-baseline-fixture-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.older = self.save(FULL, 'older full-native')
        self.anchor = self.save(FULL, 'last full-native anchor')
        self.unsafe = self.save(UNSAFE, 'unsafe incremental')
        self.safe = self.save(SAFE, 'verified incremental')
        self.head = self.save(SAFE, 'pending changes')
        self.addCleanup(patch.stopall)
        patch.dict(os.environ, {'GITHUB_RUN_ID': '99999'}).start()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def save(self, workflow, label):
        target = self.root / '.github/workflows/ci.yml'
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(workflow)
        (self.root / 'changes.txt').write_text(label + '\n')
        self.git('add', '.')
        self.git('commit', '-qm', label)
        return self.git('rev-parse', 'HEAD')

    def run_record(self, sha, run_id=1, **changes):
        return dict({'id': run_id, 'run_attempt': 2, 'head_sha': sha,
                     'event': 'push',
                     'head_branch': 'main', 'path': '.github/workflows/ci.yml',
                     'head_repository': {'full_name': REPOSITORY},
                     'status': 'completed', 'conclusion': 'success',
                     'html_url': f'https://github.com/{REPOSITORY}/actions/runs/{run_id}'}, **changes)

    def api(self, runs, conclusions=None):
        jobs = {}
        for run in runs:
            conclusion = (conclusions or {}).get(run['id'], 'success')
            jobs[f"/actions/runs/{run['id']}/attempts/{run['run_attempt']}/jobs"] = [
                {'name': 'library', 'status': 'completed', 'conclusion': 'success',
                 'run_id': run['id'], 'run_attempt': run['run_attempt'],
                 'steps': [{'name': NATIVE_STEP, 'status': 'completed', 'conclusion': conclusion},
                           {'name': FINALIZE_STEP, 'status': 'completed', 'conclusion': 'success'}]}]
        return FixtureAPI(runs, jobs)

    def choose(self, api, **kwargs):
        return select(self.root, REPOSITORY, 'main', self.head, api=api, **kwargs)

    def test_failed_native_then_static_green_keeps_last_whole_native_anchor(self):
        # The API filters failed runs; recheck them defensively if one is returned.
        runs = [self.run_record(self.head, 3),
                self.run_record(self.safe, 2, conclusion='failure'),
                self.run_record(self.anchor, 1)]
        api = self.api(runs, {3: 'skipped', 2: 'failure'})
        result = self.choose(api)
        self.assertEqual(result['base'], self.anchor)
        self.assertEqual(result['run_id'], 1)
        self.assertEqual(result['run_attempt'], 2)
        self.assertEqual(result['rejected_runs'], 2)
        self.assertIn('legacy whole-native', result['selection_reason'])
        self.assertFalse(any('/runs/2/' in path for path, _ in api.calls))

    def test_unsafe_old_incremental_success_is_not_verified(self):
        result = self.choose(self.api([self.run_record(self.unsafe, 2), self.run_record(self.anchor)]))
        self.assertEqual(result['base'], self.anchor)

    def test_valid_new_native_success_can_advance_baseline(self):
        result = self.choose(self.api([self.run_record(self.safe, 2), self.run_record(self.anchor)]))
        self.assertEqual(result['base'], self.safe)
        self.assertIn('verified CI-core', result['selection_reason'])

    def test_core_anchor_requires_finalization_and_all_versioned_commands(self):
        for conclusion in ('skipped', 'failure', None):
            api = self.api([self.run_record(self.safe)])
            next(iter(api.jobs.values()))[0]['steps'][1]['conclusion'] = conclusion
            with self.subTest(conclusion=conclusion), self.assertRaises(BaselineError):
                self.choose(api)
        self.assertIsNone(workflow_kind(SAFE.replace('ci_pipeline.py finalize', 'echo finalize')))
        self.assertIsNone(workflow_kind(UNSAFE.replace('python3 scripts/affected_scope.py',
                                                     'python3 scripts/ci_baseline.py')))

    def test_native_missing_skipped_failed_cancelled_unknown_and_duplicate_are_rejected(self):
        for conclusion in ('skipped', 'failure', 'cancelled', None, 'unknown'):
            with self.subTest(conclusion=conclusion):
                with self.assertRaisesRegex(BaselineError, 'No verified native CI ancestor'):
                    self.choose(self.api([self.run_record(self.safe)], {1: conclusion}))
        for steps in ([], [{'name': NATIVE_STEP, 'status': 'in_progress', 'conclusion': 'success'}],
                      [{'name': NATIVE_STEP, 'status': 'completed', 'conclusion': 'success'}] * 2):
            api = self.api([self.run_record(self.safe)])
            next(iter(api.jobs.values()))[0]['steps'] = steps
            with self.subTest(steps=steps), self.assertRaises(BaselineError):
                self.choose(api)

    def test_exact_attempt_and_successful_library_job_are_required(self):
        for update in ({'conclusion': 'skipped'}, {'status': 'in_progress'},
                       {'run_attempt': 1}, {'run_id': 22}, {'name': 'unrelated'}):
            api = self.api([self.run_record(self.safe)])
            next(iter(api.jobs.values()))[0].update(update)
            with self.subTest(update=update), self.assertRaises(BaselineError):
                self.choose(api)
        api = self.api([self.run_record(self.safe)])
        api.jobs['/actions/runs/1/attempts/1/jobs'] = api.jobs.pop('/actions/runs/1/attempts/2/jobs')
        with self.assertRaises(BaselineError):
            self.choose(api)

    def generic_jobs_api(self, jobs):
        api = self.api([self.run_record(self.safe)])
        api.jobs['/actions/runs/1/jobs'] = jobs
        original = api.get
        def get(path, **query):
            if path == '/actions/runs/1/attempts/2/jobs':
                raise APIUnavailable('exact-attempt route exhausted transient retries')
            return original(path, **query)
        api.get = get
        return api

    def test_unavailable_exact_route_can_use_only_explicit_unique_matching_attempt_jobs(self):
        job = next(iter(self.api([self.run_record(self.safe)]).jobs.values()))[0]
        earlier = {**job, 'run_attempt': 1}
        api = self.generic_jobs_api([earlier, job])
        result = self.choose(api)
        self.assertEqual(result['base'], self.safe)
        self.assertEqual(result['job_evidence'], {
            'endpoint': '/actions/runs/1/jobs', 'run_id': 1, 'run_attempt': 2,
            'attempt_bound_by': 'explicit job fields'})
        self.assertIn(('/actions/runs/1/jobs', {'per_page': 100, 'page': 1, 'filter': 'all'}), api.calls)

    def test_generic_fallback_rejects_wrong_missing_and_ambiguous_attempt_evidence(self):
        job = next(iter(self.api([self.run_record(self.safe)]).jobs.values()))[0]
        cases = [[{**job, 'run_attempt': 1}], [{**job, 'run_id': 2}],
                 [{k: v for k, v in job.items() if k != 'run_attempt'}],
                 [{k: v for k, v in job.items() if k != 'run_id'}], [job, job],
                 [{**job, 'steps': job['steps'] + [job['steps'][0]]}],
                 [{**job, 'steps': [job['steps'][0]]}]]
        for jobs in cases:
            with self.subTest(jobs=jobs), self.assertRaises(BaselineError):
                self.choose(self.generic_jobs_api(jobs))

    def test_permanent_api_error_does_not_switch_to_generic_jobs(self):
        api = self.generic_jobs_api([])
        original = api.get
        def get(path, **query):
            if '/attempts/' in path:
                raise BaselineError('HTTP 403')
            return original(path, **query)
        api.get = get
        with self.assertRaisesRegex(BaselineError, '403'):
            self.choose(api)
        self.assertFalse(any(path == '/actions/runs/1/jobs' for path, _ in api.calls))

    def test_current_run_nonancestor_wrong_branch_repo_and_workflow_cannot_supply_base(self):
        fork = subprocess.check_output(['git', 'commit-tree', self.git('rev-parse', self.anchor + '^{tree}'),
                                        '-p', self.older], input='fork\n', cwd=self.root, text=True).strip()
        runs = [self.run_record(self.head, 99999), self.run_record(fork, 5),
                self.run_record(self.safe, 4, head_branch='other'),
                self.run_record(self.safe, 3, head_repository={'full_name': 'other/aglib'}),
                self.run_record(self.safe, 2, path='.github/workflows/other.yml'),
                self.run_record(self.safe, 6, event='pull_request'),
                self.run_record(self.anchor)]
        self.assertEqual(self.choose(self.api(runs))['base'], self.anchor)

    def test_repository_or_default_branch_metadata_mismatch_fails(self):
        for update in ({'full_name': 'other/aglib'}, {'default_branch': 'develop'}):
            api = self.api([self.run_record(self.anchor)])
            api.metadata.update(update)
            with self.subTest(update=update), self.assertRaisesRegex(BaselineError, 'mismatch'):
                self.choose(api)

    def test_missing_git_history_and_unavailable_verified_history_fail_closed(self):
        for runs in ([], [self.run_record('a' * 40)], [self.run_record(self.unsafe)]):
            with self.subTest(runs=runs), self.assertRaises(BaselineError):
                self.choose(self.api(runs))

    def test_requested_base_may_only_widen_the_automatically_verified_range(self):
        for requested in (self.unsafe, self.head):
            with self.subTest(requested=requested), self.assertRaisesRegex(BaselineError, 'ancestor'):
                self.choose(self.api([self.run_record(self.anchor)]), requested_base=requested)
        result = self.choose(self.api([self.run_record(self.anchor)]), requested_base=self.older)
        self.assertEqual(result['base'], self.older)
        self.assertEqual(result['verified_base'], self.anchor)
        self.assertIn('widens', result['selection_reason'])

    def test_paginates_run_and_job_evidence(self):
        runs = [self.run_record(self.unsafe, i + 2) for i in range(100)] + [self.run_record(self.anchor)]
        api = self.api(runs)
        jobs_path = '/actions/runs/1/attempts/2/jobs'
        api.jobs[jobs_path] = [{'name': f'unrelated-{i}'} for i in range(100)] + api.jobs[jobs_path]
        self.assertEqual(self.choose(api)['base'], self.anchor)
        self.assertIn(('/actions/workflows/ci.yml/runs',
                       {'per_page': 100, 'page': 2, 'branch': 'main', 'status': 'success'}), api.calls)
        self.assertIn((jobs_path, {'per_page': 100, 'page': 2}), api.calls)

    def test_comments_echo_and_unsafe_full_flags_do_not_count_as_execution(self):
        for workflow in (UNSAFE + '\n# python3 scripts/ci_baseline.py\n',
                         UNSAFE.replace('python3 scripts/affected_scope.py', 'echo python3 scripts/ci_baseline.py'),
                         FULL.replace('--rehash --ci', '--rehash --ci --source-only'),
                         FULL.replace('bash scripts/check.sh --rehash --ci', '# bash scripts/check.sh --rehash --ci')):
            with self.subTest(workflow=workflow):
                self.assertIsNone(workflow_kind(workflow))

    def test_cli_outputs_evidence_and_base_without_changing_builds_caches_or_git(self):
        for path in ('.lake/build/keep.olean', '.lake/packages/keep', 'examples/downstream/.lake/build/keep'):
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b'partial native progress\x00')
        before = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob('*') if p.is_file()}
        output, github_output = Path(self.temp.name) / 'baseline.json', Path(self.temp.name) / 'github-output'
        github_output.write_text('existing=value\n')
        api = self.api([self.run_record(self.anchor)])
        with patch('ci_baseline.GitHubAPI', return_value=api), patch('ci_baseline.Path.cwd', return_value=self.root):
            with contextlib.redirect_stdout(io.StringIO()):
                status = main(['--repository', REPOSITORY, '--head', self.head,
                               '--output', str(output), '--github-output', str(github_output)])
        self.assertEqual(status, 0)
        self.assertEqual(json.loads(output.read_text())['run_url'],
                         f'https://github.com/{REPOSITORY}/actions/runs/1')
        self.assertEqual(github_output.read_text(), 'existing=value\nbase=' + self.anchor + '\n')
        after = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob('*') if p.is_file()}
        self.assertEqual(before, after)

    def test_api_failure_has_no_output_or_fallback(self):
        api = self.api([])
        api.get = lambda *args, **kwargs: (_ for _ in ()).throw(BaselineError('API unavailable'))
        output = Path(self.temp.name) / 'must-not-exist.json'
        with patch('ci_baseline.GitHubAPI', return_value=api), patch('ci_baseline.Path.cwd', return_value=self.root):
            with contextlib.redirect_stderr(io.StringIO()) as stderr:
                status = main(['--repository', REPOSITORY, '--head', self.head, '--output', str(output)])
        self.assertEqual(status, 1)
        self.assertFalse(output.exists())
        self.assertIn('API unavailable', stderr.getvalue())


class APITransportTests(unittest.TestCase):
    def test_transient_http_and_transport_failures_retry_with_small_bounds(self):
        api = GitHubAPI(REPOSITORY)
        errors = [urllib.error.HTTPError(api.url, 502, 'temporary', {}, None),
                  urllib.error.URLError('temporary disconnect'), io.BytesIO(b'{"ok": true}')]
        with patch('ci_baseline.urllib.request.urlopen', side_effect=errors) as request, \
                patch('ci_baseline.time.sleep') as sleep:
            self.assertEqual(api.get(''), {'ok': True})
        self.assertEqual(request.call_count, 3)
        self.assertEqual([call.args[0] for call in sleep.call_args_list], [1, 2])
        with patch('ci_baseline.urllib.request.urlopen', side_effect=urllib.error.URLError('still unavailable')) as request, \
                patch('ci_baseline.time.sleep'):
            with self.assertRaisesRegex(APIUnavailable, '3 attempt'):
                api.get('')
        self.assertEqual(request.call_count, 3)

    def test_tls_verification_failure_never_weakens_or_retries_validation(self):
        api = GitHubAPI(REPOSITORY)
        with patch('ci_baseline.urllib.request.urlopen', side_effect=urllib.error.URLError(
                ssl.SSLCertVerificationError('missing issuer'))) as request, \
                patch('ci_baseline.time.sleep') as sleep:
            with self.assertRaises(BaselineError):
                api.get('')
        self.assertEqual(request.call_count, 1)
        sleep.assert_not_called()
        self.assertNotIn('context', request.call_args.kwargs)

    def test_api_url_auth_and_query_and_http_errors(self):
        with patch.dict(os.environ, {'GH_TOKEN': 'fixture-token', 'GITHUB_API_URL': 'https://api.example.invalid/v3'}):
            api = GitHubAPI(REPOSITORY)
        with patch('ci_baseline.urllib.request.urlopen', return_value=io.BytesIO(b'{"workflow_runs": []}')) as request:
            self.assertEqual(api.get('/actions/workflows/ci.yml/runs', branch='main', status='success'),
                             {'workflow_runs': []})
        sent = request.call_args.args[0]
        self.assertEqual(sent.full_url,
                         'https://api.example.invalid/v3/repos/fixture/aglib/actions/workflows/ci.yml/runs?branch=main&status=success')
        self.assertEqual(sent.get_header('Authorization'), 'Bearer fixture-token')
        with patch('ci_baseline.urllib.request.urlopen', side_effect=urllib.error.HTTPError(
                sent.full_url, 403, 'rate limited', {}, None)):
            with self.assertRaisesRegex(BaselineError, 'API evidence unavailable'):
                api.get('')


if __name__ == '__main__':
    unittest.main()
