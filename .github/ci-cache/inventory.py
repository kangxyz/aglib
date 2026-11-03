#!/usr/bin/env python3
"""Read-only Linux cache size accounting, including cross-directory hardlinks."""
import argparse
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
import shutil
import signal
import stat
import time


def category(relative, native=False):
    parts = relative.parts
    if native:
        return 'auditor' if parts[:1] == ('axiom-audit',) else 'native-' + (parts[0] if parts else 'other')
    if parts[:1] == ('build',):
        return 'project-build'
    if parts[:1] == ('config',):
        return 'project-config'
    if parts[:1] == ('lint-runner',):
        return 'private-lint-tool'
    if parts[:1] == ('packages',) and len(parts) >= 2:
        if '.lake' in parts[2:]:
            offset = parts.index('.lake', 2)
            if len(parts) > offset + 1 and parts[offset + 1] in ('build', 'config'):
                return 'dependency-build/' + parts[1]
        if '.git' in parts[2:]:
            return 'dependency-git/' + parts[1]
        return 'dependency-sources/' + parts[1]
    return 'project-other'


def file_kind(path):
    name = path.name
    for suffix in ('.setup.json', '.olean.private', '.olean.server', '.ir.sig', '.ltar.hash',
                   '.olean', '.ilean', '.ltar', '.trace', '.hash', '.c', '.o', '.a', '.so'):
        if name.endswith(suffix):
            return suffix
    return path.suffix or 'extensionless'


def inventory(root, native):
    groups = defaultdict(Counter)
    kinds = defaultdict(Counter)
    inodes = {}
    largest = []
    for base, is_native in ((root / '.lake', False), (native, True)):
        if not base.is_dir():
            continue
        for current, directories, files in os.walk(base, followlinks=False):
            directories.sort()
            files.sort()
            for name in (*directories, *files):
                path = Path(current) / name
                info = path.lstat()
                group = category(path.relative_to(base), is_native)
                if stat.S_ISLNK(info.st_mode):
                    groups[group]['symlinks'] += 1
                    continue
                if not stat.S_ISREG(info.st_mode):
                    continue
                groups[group]['files'] += 1
                groups[group]['logical_bytes'] += info.st_size
                kinds[group][file_kind(path)] += info.st_size
                inode = (info.st_dev, info.st_ino)
                block_bytes = info.st_blocks * 512
                if inode not in inodes:
                    inodes[inode] = {'logical_bytes': info.st_size,
                                     'physical_bytes': block_bytes, 'groups': set()}
                    groups[group]['first_seen_unique_physical_bytes'] += block_bytes
                inodes[inode]['groups'].add(group)
                if info.st_nlink > 1:
                    groups[group]['hardlinked_paths'] += 1
                if info.st_size >= 32 * 1024 * 1024:
                    largest.append({'path': str(path), 'bytes': info.st_size,
                                    'links': info.st_nlink, 'category': group})
    crossings = defaultdict(Counter)
    for value in inodes.values():
        if len(value['groups']) > 1:
            key = ' + '.join(sorted(value['groups']))
            crossings[key]['inodes'] += 1
            crossings[key]['unique_logical_bytes'] += value['logical_bytes']
            crossings[key]['unique_physical_bytes'] += value['physical_bytes']
    usage = shutil.disk_usage(root)
    return {'schema': 1, 'root': str(root), 'native_cache': str(native),
            'groups': {k: dict(v) for k, v in sorted(groups.items())},
            'file_kinds_logical_bytes': {k: dict(v) for k, v in sorted(kinds.items())},
            'cross_group_hardlinks': {k: dict(v) for k, v in sorted(crossings.items())},
            'totals': {'paths': sum(g['files'] for g in groups.values()),
                       'logical_bytes': sum(g['logical_bytes'] for g in groups.values()),
                       'unique_inodes': len(inodes),
                       'unique_logical_bytes': sum(v['logical_bytes'] for v in inodes.values()),
                       'unique_physical_bytes': sum(v['physical_bytes'] for v in inodes.values())},
            'disk': {'total': usage.total, 'used': usage.used, 'free': usage.free},
            'largest_files': sorted(largest, key=lambda v: v['bytes'], reverse=True)[:40],
            'physical_accounting': 'st_blocks*512 counted once per device/inode; per-group ownership is first-seen and order-dependent; cross-group links reported separately'}


def sample(root, output):
    running = True
    def stop(*_):
        nonlocal running
        running = False
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    with output.open('w', buffering=1) as stream:
        while running:
            usage = shutil.disk_usage(root)
            info = os.statvfs(root)
            stream.write(json.dumps({'time': time.time(), 'total': usage.total,
                'used': usage.used, 'free': usage.free, 'free_inodes': info.f_favail}) + '\n')
            time.sleep(2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--native-cache', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--sample', action='store_true')
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.sample:
        sample(args.root, args.output)
    else:
        if args.native_cache is None:
            parser.error('--native-cache is required for inventory')
        result = inventory(args.root.resolve(), args.native_cache.resolve())
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result['totals']))


if __name__ == '__main__':
    main()
