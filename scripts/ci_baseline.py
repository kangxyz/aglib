"""Select an ancestor with successful native CI evidence; never build or fetch."""
import argparse
import json
import os
from pathlib import Path
import re
import shlex
import ssl
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request


WORKFLOW = '.github/workflows/ci.yml'
NATIVE_STEP = 'Run CI checks for the library and independent client'
FINALIZE_STEP = 'Finalize complete CI coverage'
MAX_PAGES = 10  # GitHub workflow-run searches expose at most 1,000 results.
API_ATTEMPTS = 3


class BaselineError(ValueError):
    """Missing or unsupported verification evidence."""


class APIUnavailable(BaselineError):
    """Transient transport failure exhausted its bounded retries."""


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
                   'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'aglib-ci-baseline'}
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


def library_commands(workflow):
    """Read the repository's simple library run scalars/blocks conservatively.

    This is intentionally not a general YAML interpreter. Unsupported workflow
    syntax cannot supply a baseline. Comments and command arguments containing a
    script name do not count as execution of that script.
    """
    lines = workflow.splitlines()
    start = next((i for i, line in enumerate(lines) if line == '  library:'), None)
    if start is None:
        return []
    commands = []
    index = start + 1
    while index < len(lines):
        line = lines[index]
        if line.strip() and not line.lstrip().startswith('#') and len(line) - len(line.lstrip()) <= 2:
            break
        match = re.match(r'^(\s+)(?:- )?run:\s*(.*?)\s*$', line)
        index += 1
        if not match:
            continue
        indent, value = len(match[1]), match[2]
        if re.fullmatch(r'\|[+-]?', value):
            block = []
            while index < len(lines):
                following = lines[index]
                if following.strip() and len(following) - len(following.lstrip()) <= indent:
                    break
                block.append(following.strip())
                index += 1
            value = '\n'.join(block)
        elif value.startswith(('>', '|', '"', "'")):
            continue
        for command in value.replace('\\\n', ' ').splitlines():
            try:
                tokens = shlex.split(command, comments=True)
            except ValueError:
                continue
            commands.append(tokens)
    return commands


def workflow_kind(workflow):
    commands = library_commands(workflow)
    # Fail closed for error-suppressing workflow/shell adapters.
    if 'continue-on-error:' in workflow:
        return None
    core = [cmd for cmd in commands if len(cmd) >= 3 and cmd[0] in ('python', 'python3')
            and cmd[1] == 'scripts/ci_pipeline.py']
    modes = {mode: [cmd for cmd in core if cmd[2] == mode]
             for mode in ('plan', 'source', 'native', 'finalize')}
    if all(len(rows) == 1 for rows in modes.values()):
        def option(command, name):
            return command[command.index(name) + 1] if command.count(name) == 1 and command[-1] != name else None
        calls = [rows[0] for rows in modes.values()]
        states = [option(cmd, '--state') for cmd in calls]
        plan = modes['plan'][0]
        if (states[0] and len(set(states)) == 1
                and option(plan, '--head') == '$GITHUB_SHA'
                and option(plan, '--repository') == '$GITHUB_REPOSITORY'
                and not any(token.startswith(('||', '&&', ';', '|', '&')) for cmd in calls for token in cmd)):
            return 'verified CI-core workflow'
    if 'affected_scope.py' not in workflow and ['bash', 'scripts/check.sh', '--rehash', '--ci'] in commands:
        return 'legacy whole-native workflow'
    return None


def native_success(api, run, require_finalization=False, evidence=None):
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
    library = [job for job in jobs if job.get('name') == 'library']
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
    native = [step for step in steps if step.get('name') == NATIVE_STEP]
    success = (len(native) == 1 and native[0].get('status') == 'completed'
               and native[0].get('conclusion') == 'success')
    if require_finalization:
        finalized = [step for step in steps if step.get('name') == FINALIZE_STEP]
        success = (success and len(finalized) == 1 and finalized[0].get('status') == 'completed'
                   and finalized[0].get('conclusion') == 'success')
    if success and evidence is not None:
        evidence.update(endpoint=path, run_id=run_id, run_attempt=attempt,
                        attempt_bound_by='explicit job fields' if fallback else 'exact-attempt endpoint')
    return success


def select(root, repository, default_branch, head, requested_base=None, api=None):
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
    for run in api.pages('/actions/workflows/ci.yml/runs', 'workflow_runs',
                         branch=default_branch, status='success'):
        if str(run.get('id')) == os.environ.get('GITHUB_RUN_ID'):
            continue
        if (run.get('status') != 'completed' or run.get('conclusion') != 'success'
                or run.get('head_branch') != default_branch or run.get('path') != WORKFLOW
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
        kind = workflow_kind(git(root, 'show', sha + ':' + WORKFLOW))
        job_evidence = {}
        if not kind or not native_success(api, run, kind == 'verified CI-core workflow', job_evidence):
            rejected += 1
            continue
        if not isinstance(run.get('html_url'), str) or not run['html_url'].startswith(('https://', 'http://')):
            raise BaselineError('Verified native run lacks its evidence URL')
        base = sha
        reason = f'Native library step succeeded in exact run attempt; {kind}'
        if requested_base:
            base = commit(root, requested_base)
            if not ancestor(root, base, sha):
                raise BaselineError('Requested base must be an ancestor of the automatically verified base ' + sha)
            reason += '; requested base conservatively widens the verified range'
        return {'base': base, 'head': head, 'verified_base': sha, 'repository': repository,
                'default_branch': default_branch, 'run_id': run['id'],
                'run_attempt': run['run_attempt'], 'run_url': run['html_url'],
                'selection_reason': reason, 'rejected_runs': rejected, 'job_evidence': job_evidence}
    raise BaselineError('No verified native CI ancestor found; recover successful native history explicitly. '
                        'No event.before or full-build fallback is permitted.')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--default-branch', default='main')
    parser.add_argument('--head', required=True)
    parser.add_argument('--requested-base')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--github-output', type=Path)
    args = parser.parse_args(argv)
    try:
        result = select(Path.cwd(), args.repository, args.default_branch, args.head, args.requested_base)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        if args.github_output:
            with args.github_output.open('a') as output:
                output.write('base=' + result['base'] + '\n')
    except (BaselineError, OSError) as exc:
        print('CI baseline selection failed: ' + str(exc), file=sys.stderr)
        return 1
    print(f"Verified CI baseline {result['base']} for {result['head']}: "
          f"run {result['run_id']} attempt {result['run_attempt']}; "
          f"{result['selection_reason']}; rejected {result['rejected_runs']} run(s)")
    return 0


if __name__ == '__main__':
    sys.exit(main())
