"""GitHub native-CI evidence with an explicit reviewed repository protocol."""
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import ssl
import subprocess
import time
from types import MappingProxyType
from typing import Mapping
import urllib.error
import urllib.parse
import urllib.request

MAX_PAGES = 10
API_ATTEMPTS = 3
KIND_LABELS = {'legacy': 'legacy whole-native workflow', 'core': 'verified CI-core workflow'}


class BaselineError(ValueError):
    """Missing or unsupported verification evidence."""


class APIUnavailable(BaselineError):
    """Transient transport failure exhausted its bounded retries."""


def _relative_path(path):
    return (isinstance(path, str) and bool(path) and not PurePosixPath(path).is_absolute()
            and not any(part in ('', '.', '..') for part in path.split('/')))


@dataclass(frozen=True)
class EvidenceProtocol:
    """Exact reviewed workflow/recipe identities supplied by a repository owner.

    Workflow kinds are 'legacy' or 'core'. Core recipe tuples follow the declared
    entrypoint order. Supporting-source correctness remains a separate reviewed
    trusted-producer premise; these identities are not dependency authentication.
    """
    workflow_path: str
    job_name: str
    native_step: str
    finalize_step: str | None
    workflows: Mapping[str, str]
    legacy_recipes: Mapping[str, str] = field(default_factory=dict)
    core_entrypoint_paths: tuple[str, ...] = ()
    core_recipes: frozenset[tuple[str, ...]] = frozenset()
    legacy_heads: frozenset[str] | None = None

    def __post_init__(self):
        workflows, legacy = dict(self.workflows), dict(self.legacy_recipes)
        heads = None if self.legacy_heads is None else frozenset(self.legacy_heads)
        paths = tuple(self.core_entrypoint_paths)
        recipes = frozenset(tuple(row) for row in self.core_recipes)
        sha = lambda value: isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None
        if (not _relative_path(self.workflow_path)
                or not isinstance(self.job_name, str) or not self.job_name
                or not isinstance(self.native_step, str) or not self.native_step
                or any(not sha(key) or kind not in KIND_LABELS for key, kind in workflows.items())
                or any(not _relative_path(path) or not sha(value) for path, value in legacy.items())
                or (heads is not None and any(not isinstance(value, str)
                    or re.fullmatch('[0-9a-f]{40}', value) is None for value in heads))
                or any(not _relative_path(path) for path in paths) or len(set(paths)) != len(paths)
                or any(len(row) != len(paths) or any(not sha(value) for value in row) for row in recipes)):
            raise BaselineError('Invalid reviewed evidence protocol')
        if 'legacy' in workflows.values() and not legacy:
            raise BaselineError('Legacy workflows require exact recipe identities')
        if 'core' in workflows.values() and (not paths or not isinstance(self.finalize_step, str) or not self.finalize_step):
            raise BaselineError('Core workflows require entrypoint paths and a finalization step')
        object.__setattr__(self, 'workflows', MappingProxyType(workflows))
        object.__setattr__(self, 'legacy_recipes', MappingProxyType(legacy))
        object.__setattr__(self, 'legacy_heads', heads)
        object.__setattr__(self, 'core_entrypoint_paths', paths)
        object.__setattr__(self, 'core_recipes', recipes)


class GitHubAPI:
    def __init__(self, repository):
        self.prefix = '/repos/' + repository
        self.url = os.environ.get('GITHUB_API_URL', 'https://api.github.com').rstrip('/')
        self.token = os.environ.get('GH_TOKEN') or os.environ.get('GITHUB_TOKEN')

    def get(self, path, **query):
        url = self.url + self.prefix + path
        if query:
            url += '?' + urllib.parse.urlencode(query)
        headers = {'Accept': 'application/vnd.github+json',
                   'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'lean-incremental-ci'}
        if self.token:
            headers['Authorization'] = 'Bearer ' + self.token
        for attempt in range(API_ATTEMPTS):
            try:
                with urllib.request.urlopen(urllib.request.Request(url, headers=headers),
                                            timeout=20) as response:
                    data = json.load(response)
                break
            except (OSError, ValueError) as exc:
                if isinstance(exc, ssl.SSLCertVerificationError):
                    transient, detail = False, type(exc).__name__
                elif isinstance(exc, urllib.error.HTTPError):
                    transient, detail = 500 <= exc.code < 600, f'HTTP {exc.code}'
                elif isinstance(exc, urllib.error.URLError):
                    transient = not isinstance(exc.reason, ssl.SSLCertVerificationError)
                    detail = type(exc).__name__
                else:
                    transient, detail = isinstance(exc, OSError), type(exc).__name__
                if not transient or attempt + 1 == API_ATTEMPTS:
                    # Do not print response bodies or credentials. TLS validation
                    # is unchanged; certificate errors are permanent failures.
                    error = APIUnavailable if transient else BaselineError
                    raise error(f'GitHub API evidence unavailable: {path} '
                                f'({detail}; {attempt + 1} attempt(s))') from exc
                time.sleep(attempt + 1)
        if not isinstance(data, dict):
            raise BaselineError(f'Invalid GitHub API object: {path}')
        return data

    def pages(self, path, key, **query):
        for page in range(1, MAX_PAGES + 1):
            data = self.get(path, per_page=100, page=page, **query)
            rows = data.get(key)
            if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
                raise BaselineError(f'Invalid GitHub API {key}: {path}')
            yield from rows
            if len(rows) < 100:
                return
        raise BaselineError(f'GitHub API history exceeds {MAX_PAGES * 100} {key}; narrow/recover evidence explicitly')


def git(root, *args):
    result = subprocess.run(['git', *args], cwd=root, text=True, capture_output=True)
    if result.returncode:
        raise BaselineError('Local Git evidence unavailable: git ' + ' '.join(args))
    return result.stdout.strip()


def commit(root, revision):
    if not isinstance(revision, str) or not re.fullmatch(r'[0-9a-fA-F]{40}', revision):
        raise BaselineError(f'Expected an exact 40-character commit SHA: {revision}')
    return git(root, 'rev-parse', '--verify', revision + '^{commit}')


def ancestor(root, base, head):
    result = subprocess.run(['git', 'merge-base', '--is-ancestor', base, head],
                            cwd=root, capture_output=True)
    if result.returncode not in (0, 1):
        raise BaselineError(f'Cannot establish local ancestry: {base} .. {head}')
    return result.returncode == 0


def workflow_kind(workflow, protocol):
    """Recognize exact reviewed workflow bytes, without interpreting code."""
    if isinstance(workflow, str):
        workflow = workflow.encode()
    return protocol.workflows.get(hashlib.sha256(workflow).hexdigest()) if isinstance(workflow, bytes) else None


def git_file(root, revision, path):
    result = subprocess.run(['git', 'show', revision + ':' + path], cwd=root, capture_output=True)
    return result.stdout if result.returncode == 0 else None


def reviewed_recipe(root, revision, kind, protocol):
    if kind not in KIND_LABELS:
        return None
    paths = tuple(protocol.legacy_recipes) if kind == 'legacy' else protocol.core_entrypoint_paths
    contents = {path: git_file(root, revision, path) for path in paths}
    if not paths or any(value is None for value in contents.values()):
        return None
    identities = {path: hashlib.sha256(value).hexdigest() for path, value in contents.items()}
    if kind == 'legacy':
        return identities if identities == dict(protocol.legacy_recipes) else None
    return identities if tuple(identities[p] for p in paths) in protocol.core_recipes else None


def native_success(api, run, require_finalization=False, evidence=None, *, protocol):
    attempt = run.get('run_attempt')
    run_id = run.get('id')
    if type(attempt) is not int or attempt < 1 or type(run_id) is not int or run_id < 1:
        raise BaselineError('Successful run lacks a valid id/run_attempt')
    path = f'/actions/runs/{run_id}/attempts/{attempt}/jobs'
    fallback = False
    try:
        jobs = list(api.pages(path, 'jobs'))
    except APIUnavailable:
        # The generic endpoint includes multiple attempts. Its rows themselves
        # must identify the exact successful attempt; absent fields never inherit
        # the run-list attempt by default.
        path, fallback = f'/actions/runs/{run_id}/jobs', True
        jobs = list(api.pages(path, 'jobs', filter='all'))
    library = [job for job in jobs if job.get('name') == protocol.job_name]
    if fallback:
        if any(type(job.get('run_id')) is not int or job['run_id'] != run_id
               or type(job.get('run_attempt')) is not int or job['run_attempt'] < 1 for job in library):
            return False
        library = [job for job in library if job['run_attempt'] == attempt]
    if len(library) != 1:
        return False
    job = library[0]
    if (job.get('status') != 'completed' or job.get('conclusion') != 'success'
            or type(job.get('run_id', run_id)) is not int
            or type(job.get('run_attempt', attempt)) is not int
            or job.get('run_id', run_id) != run_id
            or job.get('run_attempt', attempt) != attempt):
        return False
    steps = job.get('steps')
    if not isinstance(steps, list) or any(not isinstance(step, dict) for step in steps):
        return False
    native = [step for step in steps if step.get('name') == protocol.native_step]
    success = (len(native) == 1 and native[0].get('status') == 'completed'
               and native[0].get('conclusion') == 'success')
    if require_finalization:
        if not protocol.finalize_step:
            return False
        finalized = [step for step in steps if step.get('name') == protocol.finalize_step]
        success = (success and len(finalized) == 1 and finalized[0].get('status') == 'completed'
                   and finalized[0].get('conclusion') == 'success')
    if success and evidence is not None:
        evidence.update(endpoint=path, run_id=run_id, run_attempt=attempt,
                        attempt_bound_by='explicit job fields' if fallback else 'exact-attempt endpoint')
    return success


def select(root, repository, default_branch, head, requested_base=None, api=None, *, protocol):
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository):
        raise BaselineError('Expected repository OWNER/REPO')
    if not default_branch or default_branch.startswith('-'):
        raise BaselineError('Expected a default branch name')
    head = commit(root, head)
    api = api or GitHubAPI(repository)
    metadata = api.get('')
    if (str(metadata.get('full_name', '')).casefold() != repository.casefold()
            or metadata.get('default_branch') != default_branch):
        raise BaselineError('Repository/default-branch mismatch in GitHub API evidence')
    rejected = 0
    for run in api.pages('/actions/workflows/' + urllib.parse.quote(Path(protocol.workflow_path).name, safe='') + '/runs', 'workflow_runs',
                         branch=default_branch, status='success'):
        if str(run.get('id')) == os.environ.get('GITHUB_RUN_ID'):
            continue
        if (run.get('status') != 'completed' or run.get('conclusion') != 'success'
                or run.get('head_branch') != default_branch or run.get('path') != protocol.workflow_path
                # Pull requests can check a synthetic merge instead of head_sha.
                or run.get('event') not in ('push', 'workflow_dispatch')
                or not isinstance(run.get('head_repository'), dict)
                or str(run['head_repository'].get('full_name', '')).casefold() != repository.casefold()
                or (run.get('repository') is not None
                    and (not isinstance(run['repository'], dict)
                         or str(run['repository'].get('full_name', '')).casefold() != repository.casefold()))):
            rejected += 1
            continue
        sha = commit(root, run.get('head_sha', ''))
        if not ancestor(root, sha, head):
            rejected += 1
            continue
        workflow = git_file(root, sha, protocol.workflow_path)
        kind = workflow_kind(workflow, protocol)
        if kind == 'legacy' and protocol.legacy_heads is not None and sha not in protocol.legacy_heads:
            rejected += 1
            continue
        recipe = reviewed_recipe(root, sha, kind, protocol) if kind else None
        job_evidence = {}
        if not recipe or not native_success(api, run, kind == 'core', job_evidence, protocol=protocol):
            rejected += 1
            continue
        if not isinstance(run.get('html_url'), str) or not run['html_url'].startswith(('https://', 'http://')):
            raise BaselineError('Verified native run lacks its evidence URL')
        base = sha
        reason = f'Native library step succeeded in exact run attempt; exact reviewed {KIND_LABELS[kind]} and entrypoint recipe'
        if kind == 'legacy' and protocol.legacy_heads is not None:
            reason += '; exact reviewed legacy source commit'
        if requested_base:
            base = commit(root, requested_base)
            if not ancestor(root, base, sha):
                raise BaselineError('Requested base must be an ancestor of the automatically verified base ' + sha)
            reason += '; requested base conservatively widens the verified range'
        return {'base': base, 'head': head, 'verified_base': sha, 'repository': repository,
                'default_branch': default_branch, 'run_id': run['id'],
                'run_attempt': run['run_attempt'], 'run_url': run['html_url'],
                'selection_reason': reason, 'rejected_runs': rejected, 'job_evidence': job_evidence,
                'workflow_sha256': hashlib.sha256(workflow).hexdigest(), 'recipe_sha256': recipe}
    raise BaselineError('No verified native CI ancestor found; recover successful native history explicitly. '
                        'No event.before or full-build fallback is permitted.')


