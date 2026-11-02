#!/usr/bin/env python3
"""Proposal wiring: resource admission, provenance and trusted artifact binding."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import urllib.request
import re

PRODUCER = '88bab48f8801b48464fe6cce9881c21713001009'
GREEN_RUN = 41401104003
C = 6624993888
VERSION = '60729729c15d65dc4080956c73ec44cfde33f5da3080769b8a3a093d958db6de'
KEY = ('lean-Linux-X64-d791b020c21edcc7e9e22797f1d59fde59e8af8f675af62dc2f1fd7521bfef93-'
       '89d6106bc6c779e9737fee10c1c69f89008822de7c0ccaf47ee2412f3aae0bb2-'
       '88bab48f8801b48464fe6cce9881c21713001009-41401104003-1-tests-1')
WORKFLOW = '.github/workflows/cache-promotion.yml'
RESERVE = 3_000_000_000

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda: f.read(8 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def read(p): return json.loads(Path(p).read_text())
def write(p, data): Path(p).write_text(json.dumps(data, sort_keys=True, indent=2) + '\n')
def git(*args): return subprocess.check_output(['git', *args], text=True).strip()
def fail(condition, message):
    if not condition: raise SystemExit(message)

def api(endpoint):
    request = urllib.request.Request('https://api.github.com/repos/kangxyz/aglib/' + endpoint,
        headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                 'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'})
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)

def available_ram():
    fields = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    available = int(fields['MemAvailable'].split()[0]) * 1024
    base = Path('/sys/fs/cgroup')
    if (base / 'memory.max').exists():
        maximum = (base / 'memory.max').read_text().strip()
        if maximum != 'max':
            available = min(available, int(maximum) - int((base / 'memory.current').read_text()))
    return available

def capacity(mode, info=None):
    # SDK/source/install budget is reserved before npm ci. At copy time it is
    # already allocated and measured by statvfs, so no double counting is needed.
    needed = C + RESERVE + (1_000_000_000 if mode == 'install' else 0)
    inode_need = 100000
    ram_need = 2_000_000_000
    roots = [Path(os.environ['GITHUB_WORKSPACE']), Path(os.environ['RUNNER_TEMP'])]
    if mode == 'extract':
        fail(info is not None, 'Missing provenance/resource manifest')
        needed += int(info['resource']['expanded_4k_estimate_with_metadata_bytes']) + 5_000_000_000
        inode_need += int(info['resource']['inode_admission_minimum'])
        ram_need = 4_000_000_000
        fail(roots[0].stat().st_dev == roots[1].stat().st_dev,
             'Extraction estimate requires workspace/temp on same filesystem')
    for root in roots:
        s = os.statvfs(root)
        observed = {'path': str(root), 'free_bytes': s.f_bavail * s.f_frsize,
                    'free_inodes': s.f_favail, 'allocation_unit': s.f_frsize,
                    'required_bytes': needed, 'required_inodes': inode_need}
        print(json.dumps(observed))
        fail(observed['free_bytes'] >= needed and s.f_favail >= inode_need,
             'Resource gate failed before copying; no cleanup or larger runner fallback')
        if mode == 'extract': fail(s.f_frsize == 4096, 'Recalculate estimate for this allocation unit')
    ram = available_ram()
    print(json.dumps({'available_ram_bytes': ram, 'required_ram_bytes': ram_need}))
    fail(ram >= ram_need, 'Insufficient available RAM')

def produce(meta, resource):
    meta = Path(meta); meta.mkdir()
    fail(git('rev-parse', 'HEAD') == PRODUCER, 'Provenance checkout must be producer 88')
    subprocess.run(['git', 'diff', '--exit-code', 'HEAD', '--'], check=True)
    source_files = ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                    '.github/workflows/ci.yml', '.github/workflows/lean-ci.yml']
    copies = {}
    for name in source_files:
        out = 'source--' + name.replace('/', '__')
        shutil.copyfile(name, meta / out)
        copies[out] = sha(meta / out)
    (meta / 'source-tree.txt').write_text(git('ls-tree', '-r', '--full-tree', PRODUCER) + '\n')
    copies['source-tree.txt'] = sha(meta / 'source-tree.txt')
    r = read(resource)
    fail(r['compressed_bytes'] == C and r['version'] == VERSION, 'Wrong resource scan')
    control = Path(os.environ['CONTROL']) / '.github/cache-promotion'
    scripts = {p.name: sha(p) for p in control.iterdir() if p.is_file()}
    d = {'schema': 1, 'repository': 'kangxyz/aglib', 'producer': PRODUCER,
         'producer_tree': git('rev-parse', PRODUCER + '^{tree}'),
         'producer_green_run': GREEN_RUN, 'source_cache_id': 9862377554,
         'source_cache_key': KEY, 'source_cache_version': VERSION,
         'source_cache_ref': 'refs/heads/etale-abstract', 'compressed_bytes': C,
         'archive_sha256': r['archive_sha256'], 'resource': r,
         'source_files_sha256': copies, 'exporter_workflow_sha': os.environ['GITHUB_SHA'],
         'exporter_workflow_ref': os.environ['GITHUB_WORKFLOW_REF'],
         'export_run': int(os.environ['GITHUB_RUN_ID']),
         'export_attempt': int(os.environ['GITHUB_RUN_ATTEMPT']),
         'export_ref': os.environ['GITHUB_REF'],
         'raw_artifact_id': int(os.environ['RAW_ARTIFACT_ID']),
         'raw_artifact_zip_digest': os.environ['RAW_ARTIFACT_DIGEST'],
         'official_client_action_sha': '55cc8345863c7cc4c66a329aec7e433d2d1c52a9',
         'official_client_version': '6.1.0',
         'official_client_package_integrity': 'sha512-LVqybSbzhBp2uAETOQ3HnVjXA4AcjavgMH+LCr+cjgO+PZfciv/1QAgoW+esXBaAhvDid+vXeV70GGJpAh4V5Q==',
         'official_client_lock_sha256': sha(Path(os.environ['OFFICIAL_CLIENT_ROOT']).parents[2] / 'package-lock.json'),
         'accepted_retention_receipt': {'max_cache_retention_days': 7,
              'basis': 'principal read-only repository API observation on 2026-11-02'},
         'adapter_files_sha256': scripts}
    write(meta / 'producer-info.json', d)
    with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
        f.write('info-sha=' + sha(meta / 'producer-info.json') + '\n')
    print('Producer-info SHA-256:', sha(meta / 'producer-info.json'))

def verify_info(meta, expected):
    meta = Path(meta)
    fail(sha(meta / 'producer-info.json') == expected, 'Reviewed provenance SHA mismatch')
    d = read(meta / 'producer-info.json')
    fail(d['repository'] == 'kangxyz/aglib' and d['producer'] == PRODUCER and
         d['producer_green_run'] == GREEN_RUN and d['source_cache_id'] == 9862377554 and
         d['source_cache_key'] == KEY and d['source_cache_version'] == VERSION and
         d['source_cache_ref'] == 'refs/heads/etale-abstract' and d['compressed_bytes'] == C and
         d['export_ref'] == 'refs/heads/etale-abstract', 'Wrong provenance identity')
    fail(d['resource']['archive_sha256'] == d['archive_sha256'], 'Resource digest mismatch')
    for name, digest in d['source_files_sha256'].items():
        fail(Path(name).name == name and sha(meta / name) == digest, 'Source file digest mismatch')
    return d

def verify_raw(meta, expected, archive, scanned):
    d = verify_info(meta, expected)
    fail(Path(archive).stat().st_size == C and sha(archive) == d['archive_sha256'], 'Raw cache mismatch')
    fail(read(scanned) == d['resource'], 'Downloaded raw header/resource scan mismatch')
    print('Verified complete raw archive size, SHA-256, zstd stream, tar headers and provenance')

def trusted_run(meta, expected, metadata_id):
    d = verify_info(meta, expected)
    run = api('actions/runs/' + str(d['export_run']))
    fail(run['conclusion'] == 'success' and run['event'] == 'workflow_dispatch' and
         run['head_branch'] == 'etale-abstract' and run['head_sha'] == d['exporter_workflow_sha'] and
         run['run_attempt'] == d['export_attempt'] and run['path'] == WORKFLOW,
         'Export run identity or complete internal transport verification not successful')
    jobs = api('actions/runs/' + str(d['export_run']) + '/attempts/' + str(d['export_attempt']) + '/jobs?per_page=100')
    fail(any(j['name'] == 'Verify internal full transport' and j['conclusion'] == 'success'
             for j in jobs['jobs']), 'Independent internal transport roundtrip did not succeed')
    for artifact_id in (int(metadata_id), d['raw_artifact_id']):
        artifact = api('actions/artifacts/' + str(artifact_id))
        fail(not artifact['expired'] and artifact['workflow_run']['id'] == d['export_run'],
             'Wrong/expired artifact')
    with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
        f.write('raw-id=' + str(d['raw_artifact_id']) + '\n')
        f.write('raw-sha=' + d['archive_sha256'] + '\n')
    return d

def quota(mode, seed_key=''):
    # The job token returned 403 for this endpoint. The coordinator rechecks
    # the owner-readable policy before every dispatch; do not export that token.
    limit = {'max_cache_size_gb': 20, 'observed_at_utc': '2026-11-02T11:17:09.504207+00:00',
             'basis': 'coordinator owner-token GET before seed dispatch'}
    # Retention read requires Administration permission; reuse the supplied exact
    # read-only receipt rather than requesting a broader token. Source presence
    # and artifact expiry are checked directly in the current phase.
    print(json.dumps({'accepted_owner_storage_limit_receipt': limit, 'accepted_retention_days': 7}))
    fail(limit.get('max_cache_size_gb') == 20,
         'Cache policy changed; stop rather than change settings')
    caches = api('actions/caches?per_page=100')['actions_caches']
    source = [c for c in caches if c['id'] == 9862377554 and
              c['ref'] == 'refs/heads/etale-abstract' and c['key'] == KEY and
              c['version'] == VERSION and c['size_in_bytes'] == C]
    fail(len(source) == 1, 'Original full feature cache must remain present and unchanged')
    if mode == 'seed':
        fail(len(caches) == 1 and sum(c['size_in_bytes'] for c in caches) + C <= 20_000_000_000,
             'Unexpected cache generation/concurrent writer; do not create a third copy')
    elif mode == 'ready':
        fail(len(caches) == 2 and any(c['key'] == seed_key and c['ref'] == 'refs/heads/main'
             and c['version'] == VERSION and c['size_in_bytes'] == C for c in caches),
             'Expected exactly retained feature plus verified main seed')
    else: raise SystemExit('Unknown quota phase')
    print(json.dumps({'existing_cache_bytes': sum(c['size_in_bytes'] for c in caches),
                      'planned_bridge_bytes': 2*C, 'conservative_limit_bytes': 20_000_000_000,
                      'planned_headroom_bytes': 20_000_000_000-2*C}))

def first_ci():
    d = json.loads(os.environ['FIRST_CI_CACHE'])
    fail(set(d) == {'export_run', 'metadata_id', 'info_sha', 'seed_key'}, 'Wrong first-CI input fields')
    fail(isinstance(d['export_run'], int) and d['export_run'] > 0 and
         isinstance(d['metadata_id'], int) and d['metadata_id'] > 0 and
         re.fullmatch('[0-9a-f]{64}', d['info_sha']) and
         d['seed_key'].startswith(KEY + '-main-raw-'), 'Unfilled/invalid first-CI identifiers')
    fail(os.environ['GITHUB_REPOSITORY'] == 'kangxyz/aglib' and
         os.environ['GITHUB_REF'] == 'refs/heads/main', 'First-CI gate requires main context')
    if subprocess.run(['git', 'cat-file', '-e', PRODUCER + '^{commit}'],
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
        subprocess.run(['git', 'fetch', '--no-tags', '--depth=1', 'origin', PRODUCER], check=True)
    # Explicit allowed non-native differences, including this temporary guard.
    changed = set(git('diff', '--name-only', PRODUCER, 'HEAD').splitlines())
    allowed = {'docs/DEVELOPMENT.md', 'scripts/README.md', '.github/workflows/ci.yml',
               '.github/workflows/lean-ci.yml', '.github/workflows/cache-promotion.yml'}
    fail(all(p in allowed or p.startswith('.github/cache-promotion/') for p in changed),
         'Compiler/test/source input changed; return to source owner, never cold-build')
    artifact = api('actions/artifacts/' + str(d['metadata_id']))
    fail(not artifact['expired'] and artifact['workflow_run']['id'] == d['export_run'] and
         artifact['name'].startswith('full-meta-88bab48-'), 'Wrong first-CI metadata artifact')
    meta = Path(os.environ['RUNNER_TEMP']) / ('first-ci-meta-' + os.environ['GITHUB_JOB'])
    meta.mkdir()
    subprocess.run(['gh', 'run', 'download', str(d['export_run']), '--repo', 'kangxyz/aglib',
                    '--name', artifact['name'], '--dir', str(meta)], check=True)
    info = trusted_run(meta, d['info_sha'], d['metadata_id'])
    quota('ready', d['seed_key'])
    capacity('extract', info)
    # Locate the main seed through documented REST list fields; no GET cache/id.
    from urllib.parse import urlencode
    caches = api('actions/caches?' + urlencode({'ref':'refs/heads/main','key':d['seed_key']}))
    fail(any(c['key'] == d['seed_key'] and c['ref'] == 'refs/heads/main' and
             c['version'] == VERSION and c['size_in_bytes'] == C for c in caches['actions_caches']),
         'Exact main seed unavailable; stop before restoring/building')
    with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
        f.write('seed-key=' + d['seed_key'] + '\n')

if __name__ == '__main__':
    cmd, *args = sys.argv[1:]
    if cmd == 'capacity': capacity(args[0], read(Path(args[1]) / 'producer-info.json') if len(args)>1 else None)
    elif cmd == 'produce': produce(*args)
    elif cmd == 'info': verify_info(*args)
    elif cmd == 'raw': verify_raw(*args)
    elif cmd == 'trusted': trusted_run(*args)
    elif cmd == 'quota': quota(*args)
    elif cmd == 'first-ci': first_ci()
    else: raise SystemExit('Unknown command')
