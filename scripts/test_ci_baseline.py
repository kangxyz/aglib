"""Git/API fixtures for verified baseline selection; no Lean or cache operations."""
import contextlib
import hashlib
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

import ci_baseline as baseline
from ci_baseline import (APIUnavailable, BaselineError, FINALIZE_STEP, GitHubAPI,
                         NATIVE_STEP, main, select, workflow_kind)


REPOSITORY = 'fixture/aglib'
SOURCE_ROOT = Path(__file__).resolve().parents[1]
# Real reviewed legacy bytes, including final newlines. Tiny shell placeholders
# must not be treated as evidence of the actual historical validation recipe.
FULL = subprocess.check_output(['git', 'show', 'cc17eec:.github/workflows/ci.yml'],
                               cwd=SOURCE_ROOT, text=True)
FULL_RECIPE = subprocess.check_output(['git', 'show', 'cc17eec:scripts/check.sh'],
                                      cwd=SOURCE_ROOT, text=True)
SAFE = (SOURCE_ROOT / '.github/workflows/ci.yml').read_text()
CORE_ENTRYPOINTS = {path: (SOURCE_ROOT / path).read_bytes() for path in baseline.CORE_ENTRYPOINT_PATHS}
UNSAFE = FULL.replace('bash scripts/check.sh --rehash --ci',
                      'python3 scripts/affected_scope.py --base "$BEFORE"\n'
                      '          bash scripts/check.sh --rehash --ci --native-only --plan plan.json')


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
        # Explicit TEST-ONLY enrollment of the actual source snapshot. Production
        # admission remains empty until the principal freezes/reviews the repair.
        self.core_identity = tuple(hashlib.sha256(CORE_ENTRYPOINTS[p]).hexdigest()
                                   for p in baseline.CORE_ENTRYPOINT_PATHS)
        patch('ci_baseline.REVIEWED_CORE_RECIPES',
              baseline.REVIEWED_CORE_RECIPES | {self.core_identity}).start()
        self.write('scripts/check.sh', FULL_RECIPE.encode())
        self.older = self.save(FULL, 'older full-native')
        self.anchor = self.save(FULL, 'last full-native anchor')
        # Fixture commits are test witnesses only, never production admission.
        patch('ci_baseline.REVIEWED_LEGACY_HEADS',
              baseline.REVIEWED_LEGACY_HEADS | {self.older, self.anchor}).start()
        self.unsafe = self.save(UNSAFE, 'unsafe incremental')
        for path, contents in CORE_ENTRYPOINTS.items():
            self.write(path, contents)
        self.safe = self.save(SAFE, 'verified incremental')
        self.head = self.save(SAFE, 'pending changes')
        self.addCleanup(patch.stopall)
        patch.dict(os.environ, {'GITHUB_RUN_ID': '99999'}).start()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def write(self, path, contents):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(contents)

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

    def test_real_legacy_recipe_is_required_despite_identical_approved_workflow(self):
        self.write('scripts/check.sh', b'#!/usr/bin/env bash\nexit 0\n')
        self.head = self.save(FULL, 'same workflow with unchecked replacement recipe')
        with patch('ci_baseline.REVIEWED_LEGACY_HEADS', baseline.REVIEWED_LEGACY_HEADS | {self.head}):
            result = self.choose(self.api([self.run_record(self.head, 2), self.run_record(self.anchor)]))
        self.assertEqual(result['base'], self.anchor)
        self.assertEqual(result['recipe_sha256'], {'scripts/check.sh': baseline.LEGACY_RECIPE_SHA256})

    def test_legacy_same_workflow_and_recipe_cannot_promote_a_different_helper_source_commit(self):
        self.write('scripts/generate_imports.py', b'print("changed legacy helper")\n')
        self.head = self.save(FULL, 'same approved recipe with different helper source')
        api = self.api([self.run_record(self.head, 2), self.run_record(self.anchor)])
        result = self.choose(api)
        self.assertEqual(result['base'], self.anchor)
        self.assertEqual(result['rejected_runs'], 1)
        self.assertFalse(any('/runs/2/' in path for path, _ in api.calls))
        with patch('ci_baseline.REVIEWED_LEGACY_HEADS', baseline.REVIEWED_LEGACY_HEADS | {self.head}):
            enrolled = self.choose(self.api([self.run_record(self.head, 2)]))
        self.assertEqual(enrolled['base'], self.head)
        self.assertIn('exact reviewed legacy source commit', enrolled['selection_reason'])

    def test_missing_placeholder_or_unknown_core_entrypoint_pair_is_not_promoted(self):
        for change in ('missing', 'placeholder', 'unknown'):
            for path, contents in CORE_ENTRYPOINTS.items():
                self.write(path, contents)
            target = 'scripts/ci_state.py'
            if change == 'missing':
                (self.root / target).unlink()
            elif change == 'placeholder':
                self.write(target, b'# no-op placeholder\n')
            else:
                self.write(target, CORE_ENTRYPOINTS[target] + b'\n# unenrolled recipe revision\n')
            self.head = self.save(SAFE, 'unaccepted core recipe ' + change)
            with self.subTest(change=change):
                result = self.choose(self.api([self.run_record(self.head, 2), self.run_record(self.anchor)]))
                self.assertEqual(result['base'], self.anchor)

    def test_new_core_recipe_requires_intentional_exact_identity_enrollment(self):
        changed = CORE_ENTRYPOINTS['scripts/ci_state.py'] + b'\n# deliberate test-only enrollment\n'
        self.write('scripts/ci_state.py', changed)
        self.head = self.save(SAFE, 'new core recipe identity')
        api = lambda: self.api([self.run_record(self.head, 2), self.run_record(self.anchor)])
        self.assertEqual(self.choose(api())['base'], self.anchor)
        identity = tuple(hashlib.sha256(changed if p == 'scripts/ci_state.py' else CORE_ENTRYPOINTS[p]).hexdigest()
                         for p in baseline.CORE_ENTRYPOINT_PATHS)
        with patch('ci_baseline.REVIEWED_CORE_RECIPES', baseline.REVIEWED_CORE_RECIPES | {identity}):
            self.assertEqual(self.choose(api())['base'], self.head)

    def test_historical_owner_bytes_cannot_admit_an_unfrozen_source_head(self):
        version = baseline.HISTORICAL_CORE_RECIPES[-1]
        head = next(iter(version.heads))
        for path in version.paths:
            self.write(path, subprocess.check_output(['git', 'show', head + ':' + path], cwd=SOURCE_ROOT))
        historical_workflow = subprocess.check_output(['git', 'show', head + ':' + baseline.WORKFLOW],
                                                       cwd=SOURCE_ROOT, text=True)
        self.head = self.save(historical_workflow, 'same historical owner bytes at an unreviewed head')
        self.assertNotIn(self.head, version.heads)
        self.assertIsNone(baseline.reviewed_recipe(self.root, self.head, 'core'))
        result = self.choose(self.api([self.run_record(self.head, 2), self.run_record(self.anchor)]))
        self.assertEqual(result['base'], self.anchor)

    def test_unsafe_7e6_core_recipe_is_not_enrolled(self):
        # The rejected prototype predates the package owners. Missing owners
        # must reject it as well as an unknown complete implementation tuple.
        self.assertIsNone(baseline.reviewed_recipe(
            SOURCE_ROOT, '7e6e146e7848c713f61d93167f215230bf386124', 'core'))

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

    def test_exact_reviewed_workflow_content_is_required_including_shell_control_flow(self):
        self.assertEqual(workflow_kind(FULL), 'legacy whole-native workflow')
        self.assertEqual(workflow_kind(SAFE), 'verified CI-core workflow')
        self.assertIsNone(workflow_kind(FULL.rstrip('\n')))
        command = 'bash scripts/check.sh --rehash --ci'
        candidates = {
            'hidden conditional': FULL.replace(command, 'if false; then\n          ' + command + '\n          fi'),
            'early exit': FULL.replace(command, 'exit 0\n          ' + command),
            'suppressed error': FULL.replace(command, 'set +e\n          ' + command + '\n          true'),
            'unrelated step': FULL.replace(command, 'true').replace(
                'run: bash scripts/check.sh --source-only',
                'run: |\n          if false; then\n          ' + command + '\n          fi'),
            'unreviewed comment': SAFE + '\n# changed workflow content\n',
            'missing core phase': SAFE.replace('ci_pipeline.py finalize', 'echo finalize'),
        }
        for label, workflow in candidates.items():
            with self.subTest(label=label):
                self.assertIsNone(workflow_kind(workflow))
                self.head = self.save(workflow, label)
                result = self.choose(self.api([self.run_record(self.head, 2), self.run_record(self.anchor)]))
                self.assertEqual(result['base'], self.anchor)

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


class HistoricalCoreCorrespondenceTests(unittest.TestCase):
    def test_all_four_literal_historical_vectors_match_exact_git_heads(self):
        import ast
        old_source = subprocess.check_output(['git', 'show', '342cd1d:scripts/ci_baseline.py'],
                                            cwd=SOURCE_ROOT, text=True)
        assignment = next(node for node in ast.parse(old_source).body if isinstance(node, ast.Assign)
                          and any(isinstance(target, ast.Name) and target.id == 'REVIEWED_CORE_RECIPES'
                                  for target in node.targets))
        original_vectors = ast.literal_eval(assignment.value.args[0])
        versions = baseline.HISTORICAL_CORE_RECIPES
        self.assertEqual(len(versions), 4)
        self.assertEqual({recipe for version in versions for recipe in version.recipes}, original_vectors)
        self.assertEqual({head for version in versions for head in version.heads}, {
            'fd73486f3b9d2caaee5da270262ec3835f12b17d',
            '57c4890c4cee91a08c8808113ea0743725db741d',
            'b64c2df629c330a117c1ca84affd6dfd8a661ee1',
            '342cd1db043808e2a45ff60f6bdc728ef3058ed1'})
        for version in versions:
            self.assertEqual(len(version.paths), 23)
            self.assertEqual(len(version.heads), 1)
            identity = baseline.reviewed_recipe(SOURCE_ROOT, next(iter(version.heads)), 'core')
            self.assertIsNotNone(identity)
            self.assertIn(tuple(identity[path] for path in version.paths), version.recipes)

    def test_current_full_owner_vector_and_coverage_workflow_match_actual_reviewed_bytes(self):
        paths = baseline.CORE_ENTRYPOINT_PATHS
        self.assertEqual(len(paths), 28)
        self.assertEqual(paths[:23], baseline.HISTORICAL_CORE_ENTRYPOINT_PATHS)
        self.assertEqual(paths[23:], tuple('ci/lean_ci/' + name + '.py'
                         for name in ('execution', 'local', 'recipe', 'mappings', 'frozen')))
        actual = tuple(hashlib.sha256((SOURCE_ROOT / path).read_bytes()).hexdigest() for path in paths)
        self.assertEqual(baseline.REVIEWED_CORE_RECIPES, frozenset({actual}))
        self.assertEqual(actual[-1], '80806de1992ace1d0538ed97ac67796ed5e0f85c5b769553be749f07b6d9af1e')
        workflow_hash = hashlib.sha256((SOURCE_ROOT / baseline.WORKFLOW).read_bytes()).hexdigest()
        self.assertEqual(workflow_hash, 'e98acc7b5268361080b1e71642db9c6791dadb8a5e90d9d44258fe00f4f08a1c')
        self.assertEqual(baseline.REVIEWED_WORKFLOWS[workflow_hash], 'verified CI-core workflow')
        self.assertEqual(baseline.REVIEWED_WORKFLOWS['3dca194bb4d22a3569c6dc77bc2e609d30390feb3e40bcdfa03c112acc445407'],
                         'verified CI-core workflow')
        self.assertEqual(baseline.REVIEWED_LEGACY_HEADS, frozenset({'cc17eecf0344f15c89ffc04cade60b1b09cf9f43'}))
        self.assertEqual(baseline.LEGACY_RECIPE_SHA256, '441bb18419661c8dff622f6b23b75332d2c0e58eba26f0b47e751be003fc5ad2')


if __name__ == '__main__':
    unittest.main()
