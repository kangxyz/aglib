#!/usr/bin/env python3
"""PROPOSAL ONLY: bounded streaming raw cache-header/resource discovery."""
import hashlib
import json
import os
from pathlib import Path
import posixpath
import subprocess
import sys
import tarfile
import resource

archive, output = map(Path, sys.argv[1:])
workspace = '/home/runner/work/aglib/aglib'
native = '/home/runner/work/_temp/lake-native-cache'
roots = (workspace + '/.lake', native)
def allowed(name):
    p = posixpath.normpath(posixpath.join(workspace, name))
    if len(name.encode()) > 4096 or not any(p == r or p.startswith(r + '/') for r in roots):
        raise SystemExit('Unexpected cache member/link destination: ' + name)
    return p

def resolved(name, links, follow_leaf=True):
    # Resolve components before '..', as a filesystem does; lexical normpath
    # alone is insufficient when a previous component is a symlink.
    pending = posixpath.join(workspace, name).split('/')
    current = []
    hops = 0
    while pending:
        part = pending.pop(0)
        if part in ('', '.'): continue
        if part == '..':
            if current: current.pop()
            continue
        candidate = '/' + '/'.join(current + [part])
        if candidate in non_dirs and pending:
            raise SystemExit('Unsupported link/member traverses a regular-file parent')
        if candidate in links and (follow_leaf or pending):
            hops += 1
            if hops > 40: raise SystemExit('Unsupported cyclic/deep symlink chain')
            target = links[candidate]
            if target.startswith('/'): current = []
            pending = target.split('/') + pending
        else:
            current.append(part)
    return '/' + '/'.join(current), hops

sha = hashlib.sha256()
with archive.open('rb') as stream:
    for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
        sha.update(chunk)
count = regular = expanded = max_name = 0
seen_roots = set()
members = []
member_paths = set()
links = {}
targets = []
regular_paths = {}
hardlinks = []
non_dirs = set()
# Linux Actions process bound: oversized malicious metadata fails closed rather
# than consuming unbounded RAM. Decoder is single-threaded with a window limit.
if sys.platform.startswith('linux'):
    resource.setrlimit(resource.RLIMIT_AS, (2_000_000_000, 2_000_000_000))
proc = subprocess.Popen(['zstd', '-dc', '--memory=256MB', str(archive)], stdout=subprocess.PIPE)
try:
    with tarfile.open(fileobj=proc.stdout, mode='r|') as tar:
        for m in tar:
            dest = allowed(m.name)
            if dest in member_paths: raise SystemExit('Unsupported duplicate archive member')
            member_paths.add(dest)
            members.append(m.name)
            seen_roots.update(r for r in roots if dest == r or dest.startswith(r + '/'))
            count += 1
            max_name = max(max_name, len(m.name.encode()))
            if count > 2_000_000:
                raise SystemExit('Entry-count resource limit')
            if m.isreg():
                regular_paths[dest] = count
                non_dirs.add(dest)
                regular += m.size
                expanded += ((m.size + 4095) // 4096) * 4096
            elif m.issym():
                target = m.linkname if m.linkname.startswith('/') else posixpath.join(posixpath.dirname(m.name), m.linkname)
                allowed(target)
                if dest in links: raise SystemExit('Unsupported duplicate symlink member')
                links[dest] = m.linkname
                targets.append(target)
            elif m.islnk():
                allowed(m.linkname)
                targets.append(m.linkname)
                hardlinks.append((m.linkname, count))
                non_dirs.add(dest)
            elif not m.isdir():
                raise SystemExit('Unsupported special cache file')
            # Bound header-memory retention; bodies are consumed/discarded by r|.
            tar.members.clear()
        while proc.stdout.read(8 * 1024 * 1024):
            pass
    if proc.wait() or seen_roots != set(roots):
        raise SystemExit('Corrupt/incomplete archive or missing root')
    for name in members:
        dest, hops = resolved(name, links, follow_leaf=False)
        allowed(dest)
        if hops: raise SystemExit('Unsupported archive member traverses a symlink parent')
    for target, index in hardlinks:
        dest, hops = resolved(target, links, follow_leaf=False)
        if hops or dest not in regular_paths or regular_paths[dest] >= index:
            raise SystemExit('Unsupported hardlink target: require earlier regular archive member')
    for target in targets:
        dest, _ = resolved(target, links)
        allowed(dest)
finally:
    if proc.poll() is None:
        proc.kill()
    proc.wait()
expanded += count * 8192  # conservative directory/inode/name/metadata allowance
d = {'repository': 'kangxyz/aglib', 'producer': '88bab48f8801b48464fe6cce9881c21713001009',
     'source_cache_id': 9862377554, 'source_cache_ref': 'refs/heads/etale-abstract',
     'version': '60729729c15d65dc4080956c73ec44cfde33f5da3080769b8a3a093d958db6de',
     'compression': 'zstd-without-long', 'paths': ['./.lake', native],
     'archive_sha256': sha.hexdigest(), 'compressed_bytes': archive.stat().st_size,
     'regular_logical_bytes': regular, 'entries': count, 'max_path_bytes': max_name,
     'expanded_4k_estimate_with_metadata_bytes': expanded,
     'inode_admission_minimum': count + 100000,
     'conditions': ['4 KiB allocation blocks', 'same backing filesystem for both trees',
                    'in-root link resolution only; member paths through symlink parents are unsupported',
                    'hardlinks must target an earlier regular member directly, not another link',
                    'includes 8192 bytes extra per entry; add toolchain/setup/free-space reserve',
                    'actual native no-build applicability remains unchecked']}
output.write_text(json.dumps(d, sort_keys=True, indent=2) + '\n')
print(json.dumps(d, sort_keys=True))
