#!/usr/bin/env python3
"""One-time first-CI staging gates; no compilation, deletion or service write."""
import json
import os
from pathlib import Path
import stat
import sys
import tarfile
from promotion import RESERVE, api, available_ram, fail, read, write

temp = Path(os.environ['RUNNER_TEMP'])
native = Path(os.environ.get('LAKE_CACHE_DIR', str(temp/'lake-native-cache')))

def tree(paths):
    logical = allocated = tar_bytes = count = files = 0
    for root in paths:
        fail(root.exists() and not root.is_symlink(), 'Missing/linked staging input: ' + str(root))
        todo = [root]
        while todo:
            p = todo.pop(); s = p.lstat(); count += 1
            fail(len(str(p).encode()) <= 4096, 'Unsupported staging path length')
            if stat.S_ISDIR(s.st_mode): todo.extend(p.iterdir())
            else:
                fail(stat.S_ISREG(s.st_mode), 'Unsupported staging link/special file: ' + str(p))
                files += 1; logical += s.st_size
                allocated += ((s.st_size + 4095)//4096)*4096
                tar_bytes += ((s.st_size + 511)//512)*512
    # Per-entry name/header/metadata slack, plus end-of-archive record padding.
    return {'logical': logical, 'allocated': allocated + count*8192,
            'tar_bound': tar_bytes + count*8192 + 10240, 'count': count, 'files': files}

def admit(label, extra, inodes, memory=2_000_000_000):
    fail(not (temp/'full-cache-raw/cache.tzst').exists(),
         'Opaque transport archive must not coexist with first-CI staging')
    fail(not os.environ.get('TAR_OPTIONS'), 'Unsupported inherited TAR_OPTIONS')
    for root in (Path(os.environ['GITHUB_WORKSPACE']), temp):
        s = os.statvfs(root)
        d = {'phase': label, 'path': str(root), 'free_bytes': s.f_bavail*s.f_frsize,
             'required_extra_bytes': extra + RESERVE, 'free_inodes': s.f_favail,
             'required_extra_inodes': inodes + 100000}
        print(json.dumps(d))
        fail(s.f_frsize == 4096 and d['free_bytes'] >= extra + RESERVE and
             s.f_favail >= inodes + 100000, 'First-CI staging resource gate failed before operation')
    fail(available_ram() >= memory, 'Insufficient live RAM before first-CI staging')

def stage_copy():
    # Pinned Lake 4.34.1 stage copies the map and a subset of artifactDir files.
    a = tree([native/'artifacts'])
    mapping = temp/'outputs.jsonl'
    fail(mapping.is_file() and not mapping.is_symlink(), 'Missing regular outputs mapping')
    fail(not (temp/'cache-staging').exists(), 'Expected empty first-CI stage destination')
    upper = a['allocated'] + mapping.stat().st_size + 1_048_576 + 4*8192
    # Covers complete copied subset and a full uncompressed tar simultaneously.
    admit('stage-copy-and-tar', 2*upper + 10240, 2*a['count']+16,
          max(2_000_000_000, 64*mapping.stat().st_size))
    write(temp/'first-ci-stage-bound.json', {'logical': a['logical'] + mapping.stat().st_size + 1_048_576,
                                           'files': a['files'] + 2})

def stage_tar():
    a = tree([temp/'cache-staging']); bound = read(temp/'first-ci-stage-bound.json')
    fail(a['logical'] <= bound['logical'] and a['files'] <= bound['files'],
         'Native staging exceeded measured artifact/map envelope')
    admit('stage-native-tar', a['tar_bound'], 2)

def dependencies():
    a = tree([native/'artifacts', native/'outputs'])
    # A hard output-file cap, not an assertion about the compression ratio.
    cap = 2*a['tar_bound'] + 1_048_576
    fail(not (temp/'build-dependencies.tar.zst').exists(), 'Expected fresh dependency snapshot file')
    admit('dependency-zstd-snapshot', cap, 2)
    write(temp/'first-ci-dependency-bound.json', {'file_blocks': cap//1024, 'cap_bytes': cap})

def stage_download(destination, label):
    artifacts = api('actions/runs/' + os.environ['GITHUB_RUN_ID'] + '/artifacts?per_page=100')['artifacts']
    matches = [a for a in artifacts if a['name'] == 'cache-staging' and not a['expired']]
    fail(len(matches) == 1, 'Expected one mandatory current-run production artifact')
    size = matches[0]['size_in_bytes']
    fail(size > 0, 'Empty current-run staging artifact')
    # Fixed reviewed workflow uses ZIP compression-level 0: contained tar <= ZIP.
    # Admit only this download; inspect real tar headers before any extraction.
    fail(not os.path.lexists(destination), 'Expected fresh stage transport file')
    admit(label, ((size+4095)//4096)*4096, 2)
    return {'artifact_id': matches[0]['id'], 'zip_bytes': size}

def test_download():
    stage_download(native/'lake-native-cache.tar', 'test-stage-download-only')

def publish_download():
    bound = stage_download(Path(os.environ['GITHUB_WORKSPACE'])/'lake-native-cache.tar',
                           'publish-stage-download-only')
    write(temp/'first-ci-publish-bound.json', bound)

def publish_upload(name):
    fail(Path(name).name == name and name.endswith('.tar'), 'Unexpected release asset path')
    asset = Path(os.environ['GITHUB_WORKSPACE'])/name
    fail(asset.is_file() and not asset.is_symlink(), 'Missing regular release asset')
    bound = read(temp/'first-ci-publish-bound.json')
    fail(0 < asset.stat().st_size <= bound['zip_bytes'], 'Release asset exceeds admitted stage artifact')
    # The existing mv is same-directory rename; release upload streams this file.
    # Its disk allocation is already reflected in statvfs; reserve RAM and free
    # filesystem margin, without another tar/ZIP copy or any extraction.
    admit('publish-existing-asset-upload', 0, 2)
    print(json.dumps({'phase':'publish-existing-asset-upload', 'asset_bytes':asset.stat().st_size,
                      'source_artifact_id':bound['artifact_id']}))

def test_extract():
    archive = native/'lake-native-cache.tar'
    fail(archive.is_file() and not archive.is_symlink(), 'Missing regular mandatory staging tar')
    count = logical = allocated = mapping_size = 0
    seen = set()
    with tarfile.open(archive, mode='r:') as tar:
        for m in tar:
            name = m.name.removeprefix('./').rstrip('/')
            fail(m.isdir() and name == '' or m.isreg() and '/' not in name and name not in ('', '.', '..'),
                 'Unsupported non-flat native stage member')
            fail(name not in seen, 'Duplicate native stage member/mapping')
            seen.add(name)
            count += 1
            if m.isreg():
                logical += m.size; allocated += ((m.size+4095)//4096)*4096
                if name == 'outputs.jsonl': mapping_size = m.size
    fail({'outputs.jsonl','producer.json'} <= seen and mapping_size > 0,
         'Missing unique nonempty native output map or producer record')
    fail(not (temp/'cache-staging').exists(), 'Expected fresh Test stage directory')
    # Existing tar already occupies disk: reserve expanded stage, replacement
    # artifact copies and map-write slack, not an inferred cache expansion ratio.
    admit('test-stage-extract-unstage', 3*allocated + 3*count*8192, 3*count,
          max(2_000_000_000, 64*mapping_size))

if __name__ == '__main__':
    commands = {'stage-copy': stage_copy, 'stage-tar': stage_tar, 'dependencies': dependencies,
                'test-download': test_download, 'test-extract': test_extract,
                'publish-download': publish_download}
    if len(sys.argv) == 3 and sys.argv[1] == 'publish-upload': publish_upload(sys.argv[2])
    else:
        fail(len(sys.argv) == 2 and sys.argv[1] in commands, 'Unknown first-CI resource phase')
        commands[sys.argv[1]]()
