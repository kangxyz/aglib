"""Accept common native producer evidence, or initialize its uncovered obligations.

A green caller is insufficient. The referenced reusable workflow must match the
single common release template and executing core, and its exact successful run
attempt must complete the canonical native and finalization steps. Old Lake
artifacts remain usable independently of this checker-coverage decision.
"""
import base64
import binascii
import hashlib
import os
from pathlib import Path
import re
from types import SimpleNamespace
import tomllib

from .github import BaselineError, GitHubAPI, ancestor, commit, git, git_file, native_success

PRODUCER = 'kangxyz/aglib'
WORKFLOW = '.github/workflows/lean-ci.yml'
PROFILE = 'canonical-origin-v1'
NATIVE_STEP = 'Canonical native checks (canonical-origin-v1)'
FINALIZE_STEP = 'Finalize canonical coverage (canonical-origin-v1)'
# One central workflow identity, with its acyclic core-commit pins normalized.
# This is deliberately not a collection of consumer workflow/recipe hashes.
COMMON_TEMPLATE_SHA256 = '85a5aa80d132f28102b5f0371749c8f0c2d1630e0943156512bb1421bade3e3e'
SHA = re.compile(r'[0-9a-f]{40}')
CORE_PIN = re.compile(rb'(?m)^          ref: ([0-9a-f]{40})$')
CALL = re.compile(r'(?m)^    uses: (\./\.github/workflows/lean-ci\.yml|kangxyz/aglib/\.github/workflows/lean-ci\.yml@[0-9a-f]{40})\s*$')


def core_revision():
    """The hosted workflow uses the pinned core checkout through PYTHONPATH."""
    directory = Path(git(Path(__file__).resolve().parent, 'rev-parse', '--show-toplevel'))
    return commit(directory, git(directory, 'rev-parse', 'HEAD'))


def _workflow(source, core):
    if not isinstance(source, bytes):
        return False
    pins = CORE_PIN.findall(source)
    if not pins or set(pins) != {core.encode()}:
        return False
    normalized = CORE_PIN.sub(b'          ref: PENDING_COMMON_CORE_REVISION', source)
    return hashlib.sha256(normalized).hexdigest() == COMMON_TEMPLATE_SHA256


def _caller(source, repository, revision, config_path):
    """Read only the deliberately small caller interface, not arbitrary YAML.

    Reject unsupported aliases/quoted job names/name overrides conservatively.
    The actual executable producer is authenticated by the common template.
    """
    if source is None:
        return None
    try:
        text = source.decode('utf-8')
    except UnicodeDecodeError:
        return None
    calls = list(CALL.finditer(text))
    if len(calls) != 1:
        return None
    call = calls[0]
    # Only a direct top-level jobs entry may establish the native job prefix.
    before = text[:call.start()]
    jobs = before.rfind('\njobs:\n')
    if jobs < 0:
        return None
    headers = list(re.finditer(r'(?m)^  ([A-Za-z_][A-Za-z0-9_-]*):\s*$', before[jobs:]))
    if not headers:
        return None
    header = headers[-1]
    job = header.group(1)
    start = jobs + header.start()
    following = re.search(r'(?m)^  [A-Za-z_][A-Za-z0-9_-]*:\s*$', text[call.end():])
    end = call.end() + following.start() if following else len(text)
    block = text[start:end]
    if re.search(r'(?m)^    name:', block):
        return None
    configs = re.findall(r'(?m)^      config: ([A-Za-z0-9_./-]+)\s*$', block)
    if len(configs) > 1 or (configs[0] if configs else '.github/lean-ci.toml') != config_path:
        return None
    reference = call.group(1)
    if reference.startswith('./'):
        if repository.casefold() != PRODUCER.casefold():
            return None
        release = revision
    else:
        release = reference.rsplit('@', 1)[1]
    return job, release, reference.startswith('./')


def _contents(api, path, revision):
    data = api.get('/contents/' + path, ref=revision)
    if (data.get('type') != 'file' or data.get('encoding') != 'base64'
            or not isinstance(data.get('content'), str)):
        raise BaselineError('Invalid pinned common workflow source response')
    try:
        return base64.b64decode(''.join(data['content'].split()), validate=True)
    except (ValueError, binascii.Error) as error:
        raise BaselineError('Invalid pinned common workflow source encoding') from error


def _run_matches(run, repository, default_branch):
    return (run.get('status') == 'completed' and run.get('conclusion') == 'success'
        and run.get('head_branch') == default_branch
        and run.get('event') in {'push', 'workflow_dispatch'}
        and isinstance(run.get('head_repository'), dict)
        and str(run['head_repository'].get('full_name', '')).casefold() == repository.casefold()
        and isinstance(run.get('repository'), dict)
        and str(run['repository'].get('full_name', '')).casefold() == repository.casefold())


def select_baseline(root, repository, default_branch, head, requested_base=None,
                    api=None, config=None):
    """Return verified common coverage or honest absence; API errors propagate.

    Only a requested ancestor of an accepted native baseline may widen its range.
    Initialization never invents base/verified_base fields. The configured scope
    then rederives the current universe, and Progress subtracts compatible checks.
    """
    if not isinstance(repository, str) or not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository):
        raise BaselineError('Expected repository OWNER/REPO')
    if not isinstance(default_branch, str) or not default_branch or default_branch.startswith('-'):
        raise BaselineError('Expected a default branch name')
    head = commit(root, head)
    api = api or GitHubAPI(repository)
    metadata = api.get('')
    if (str(metadata.get('full_name', '')).casefold() != repository.casefold()
            or metadata.get('default_branch') != default_branch):
        raise BaselineError('Repository/default-branch mismatch in GitHub API evidence')
    config_path = (config or {}).get('config_path', '.github/lean-ci.toml')
    core = core_revision()
    producer_api = None
    releases = {}
    decision = {'head': head, 'repository': repository, 'default_branch': default_branch}
    for listed in api.pages('/actions/runs', 'workflow_runs', branch=default_branch, status='success'):
        if str(listed.get('id')) == os.environ.get('GITHUB_RUN_ID'):
            continue
        if not _run_matches(listed, repository, default_branch):
            continue
        path = listed.get('path')
        if not isinstance(path, str) or not re.fullmatch(r'\.github/workflows/[A-Za-z0-9_.-]+\.ya?ml', path):
            continue
        sha = commit(root, listed.get('head_sha', ''))
        if not ancestor(root, sha, head):
            continue
        caller = _caller(git_file(root, sha, path), repository, sha, config_path)
        if caller is None:
            continue
        job, release, local = caller
        # Old non-common configurations cannot become canonical profile evidence.
        source_config = git_file(root, sha, config_path)
        try:
            schema = tomllib.loads(source_config.decode()) if source_config is not None else {}
        except (UnicodeDecodeError, tomllib.TOMLDecodeError):
            continue
        if type(schema.get('schema')) is not int or schema['schema'] != 1:
            continue
        run_id, attempt = listed.get('id'), listed.get('run_attempt')
        if type(run_id) is not int or run_id < 1 or type(attempt) is not int or attempt < 1:
            raise BaselineError('Common run lacks an exact id/run_attempt')
        run = api.get(f'/actions/runs/{run_id}')
        if (not _run_matches(run, repository, default_branch)
                or any(run.get(k) != listed.get(k) for k in ('id', 'run_attempt', 'head_sha', 'path'))):
            continue  # A newer/incomplete rerun cannot inherit the listed attempt.
        references = run.get('referenced_workflows')
        if not isinstance(references, list) or any(not isinstance(r, dict) for r in references):
            raise BaselineError('Common run lacks referenced_workflows metadata')
        prefix = PRODUCER + '/' + WORKFLOW + '@'
        matches = [r for r in references if isinstance(r.get('path'), str) and r['path'].startswith(prefix)
                   and r.get('sha') == release
                   and (local or r['path'] == prefix + release)]
        if len(matches) != 1:
            continue
        if release not in releases:
            if local:
                workflow = git_file(root, sha, WORKFLOW)
            else:
                if producer_api is None:
                    producer_api = api if repository.casefold() == PRODUCER.casefold() else GitHubAPI(PRODUCER)
                workflow = _contents(producer_api, WORKFLOW, release)
            releases[release] = _workflow(workflow, core)
        if not releases[release]:
            continue
        evidence = {}
        protocol = SimpleNamespace(job_name=job + ' / native', native_step=NATIVE_STEP,
                                   finalize_step=FINALIZE_STEP)
        if not native_success(api, run, require_finalization=True, evidence=evidence, protocol=protocol):
            continue
        base = sha
        if requested_base:
            base = commit(root, requested_base)
            if not ancestor(root, base, sha):
                raise BaselineError('Requested base must be an ancestor of the verified native base ' + sha)
        return dict(decision, kind='verified', base=base, verified_base=sha,
                    run_id=run_id, run_attempt=attempt, profile=PROFILE,
                    common_release=release, common_core=core, job_evidence=evidence)
    if requested_base:
        raise BaselineError('Requested base cannot substitute for absent verified common native coverage')
    return dict(decision, kind='initial', profile=PROFILE,
                selection_reason='No accepted common native ancestor; derive the current required universe')
