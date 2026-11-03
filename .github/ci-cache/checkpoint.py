#!/usr/bin/env python3
"""CI-only scoped working-build checkpoints; native Lake remains the validity gate.

Archives contain regular generated files and an integrity/coverage manifest. They
are compilation accelerators from trusted producers, never successful-check
receipts. No source checkout, Git state or whole Lake content store is copied.
"""
import argparse
from contextlib import contextmanager
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile

SCHEMA = 1
LAYERS = ('root', 'dependencies', 'tools')
AUDITOR_PIN = '46024e005996495c65ef609368e11ab39c4222e3'


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def file_hash(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def relative(value):
    if not isinstance(value, str) or not value or '\\' in value:
        raise ValueError('invalid relative checkpoint path')
    path = PurePosixPath(value)
    if path.is_absolute() or any(p in ('', '.', '..') for p in value.split('/')):
        raise ValueError('absolute or traversing checkpoint path: ' + value)
    return path


def contained(base, name):
    path = base.joinpath(*relative(name).parts)
    for part in [base, *path.parents]:
        if part == base.parent:
            break
        if part.is_symlink():
            raise ValueError('symlink in checkpoint path: ' + str(part))
        if part == base:
            break
    # Check all descendants explicitly; do not follow a symlink into source paths.
    current = base
    for component in path.relative_to(base).parts:
        current /= component
        if current.is_symlink():
            raise ValueError('symlink in checkpoint path: ' + str(current))
    return path


def configuration(root):
    import tomllib
    file = root / 'lakefile.toml'
    return tomllib.loads(file.read_text()) if file.is_file() else {}


def dependencies(root):
    """Only resolved, repository-contained package directories are admitted."""
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = []
    directory = manifest.get('packagesDir', '.lake/packages')
    relative(directory)
    for item in manifest['packages']:
        if item['type'] == 'git':
            name = str(relative(directory) / relative(item['name']))
            if item.get('subDir'):
                name += '/' + str(relative(item['subDir']))
        elif item['type'] == 'path':
            value = Path(item['dir'])
            if value.is_absolute():
                try:
                    name = value.relative_to(root).as_posix()
                except ValueError as error:
                    raise ValueError('external path dependency is not checkpointable') from error
            else:
                name = str(relative(item['dir']))
        else:
            raise ValueError('unsupported resolved dependency type')
        path = contained(root, name)
        if path == root or path in packages:
            raise ValueError('duplicate/root dependency directory')
        packages.append(path)
    return sorted(packages)


def contexts(root):
    inputs = {}
    for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean',
                 '.lake/package-overrides.json'):
        path = contained(root, name)
        inputs[name] = file_hash(path) if path.is_file() else None
    # Runtime identity plus resolved pins/configuration, not changing proof sources.
    value = {'schema': SCHEMA, 'system': platform.system(), 'machine': platform.machine(),
             'inputs': inputs}
    common = digest(value)
    tools = {}
    for directory in (root / '.github/lint', root / 'scripts/lean_tools/_lint'):
        if directory.is_dir():
            for path in sorted(directory.iterdir()):
                if path.is_file() and not path.is_symlink():
                    tools[path.relative_to(root).as_posix()] = file_hash(path)
    return {'root_context': common, 'dependencies_context': common,
            'tools_context': digest({'base': common, 'tools': tools, 'auditor': AUDITOR_PIN})}


def tree(path):
    if not path.exists():
        return
    if path.is_symlink():
        raise ValueError('symlinked checkpoint scope: ' + str(path))
    if path.is_file():
        yield path
        return
    for current, children, files in os.walk(path, followlinks=False):
        children.sort()
        for name in [*children, *sorted(files)]:
            entry = Path(current) / name
            if entry.is_symlink():
                raise ValueError('symlinked generated output: ' + str(entry))
        for name in sorted(files):
            entry = Path(current) / name
            if not stat.S_ISREG(entry.stat().st_mode):
                raise ValueError('nonregular generated output: ' + str(entry))
            yield entry


def allowed_scopes(root, layer, native):
    scopes = []
    if layer == 'root':
        scopes += [('workspace', root / '.lake/build'), ('workspace', root / '.lake/config')]
    if layer in ('dependencies', 'tools'):
        for package in dependencies(root):
            scopes += [('workspace', package / '.lake/build'), ('workspace', package / '.lake/config')]
    if layer == 'tools':
        private = root / '.lake/lint-runner'
        scopes += [('workspace', private / '.lake/build'), ('workspace', private / '.lake/config')]
        scopes += [('workspace', private / name) for name in
                   ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json', 'BatchedLint.lean')]
        scopes += [('native', native / 'axiom-audit/.lake/build'),
                   ('native', native / 'axiom-audit/.lake/config')]
    return scopes


def info(base, path, area):
    name = path.relative_to(base).as_posix()
    contained(base, name)
    before = path.stat()
    value = {'area': area, 'path': name, 'size': before.st_size,
             'mode': stat.S_IMODE(before.st_mode) & 0o777,
             'mtime_ns': before.st_mtime_ns, 'sha256': file_hash(path)}
    after = path.stat()
    if (before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != \
            (after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
        raise ValueError('generated file changed during checkpoint scan: ' + name)
    return value


def semantic(entry):
    return {k: v for k, v in entry.items() if k != 'mtime_ns'}


def snapshot(root, layer, native, production):
    baseline = {}
    if layer == 'tools':
        saved = root / '.lake/ci-cache/dependencies.json'
        data = json.loads(saved.read_text())
        if data.get('context') != contexts(root)['dependencies_context'] or data.get('layer') != 'dependencies':
            raise ValueError('tools need the matching CURRENT dependency baseline manifest')
        baseline = {(e['area'], e['path']): semantic(e) for e in data['entries']}
    entries = {}
    for area, directory in allowed_scopes(root, layer, native):
        base = root if area == 'workspace' else native
        for path in tree(directory):
            rel = path.relative_to(base).as_posix()
            entry = info(base, path, area)
            key = (area, rel)
            if layer == 'tools' and key in baseline and semantic(entry) == baseline[key]:
                continue
            entries[key] = entry
    return sorted(entries.values(), key=lambda e: (e['area'], e['path']))


@contextmanager
def archive_stream(path, writing):
    """Stream zstd on Linux; no simultaneous expanded tar is required."""
    if path.name.endswith('.tar.zst'):
        if writing:
            with path.open('wb') as target:
                process = subprocess.Popen(['zstd', '-q', '-T2', '-1', '-c'],
                                           stdin=subprocess.PIPE, stdout=target)
                stream = process.stdin
                try:
                    yield stream
                finally:
                    stream.close()
                    code = process.wait()
                    if code:
                        raise ValueError('checkpoint zstd compression failed')
        else:
            process = subprocess.Popen(['zstd', '-q', '-d', '-c', str(path)], stdout=subprocess.PIPE)
            try:
                yield process.stdout
            finally:
                process.stdout.close()
                code = process.wait()
                if code:
                    raise ValueError('checkpoint zstd decompression failed')
    else:
        with path.open('wb' if writing else 'rb') as stream:
            yield stream


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(data, sort_keys=True) + '\n')
    os.replace(temporary, path)


def emit(data, output=None):
    print(json.dumps(data, sort_keys=True), flush=True)
    if output:
        with Path(output).open('a') as stream:
            for name, value in data.items():
                if isinstance(value, (str, int, bool)):
                    text = str(value).lower() if isinstance(value, bool) else str(value)
                    if '\n' in text or '\r' in text:
                        raise ValueError('multiline action output')
                    stream.write(f'{name}={text}\n')


def pack(args):
    root, native = args.root, args.native_cache
    layer = args.layer
    entries = snapshot(root, layer, native, args.production_root)
    context = contexts(root)[layer + '_context']
    generation = digest([semantic(e) for e in entries])
    metadata = {'schema': SCHEMA, 'layer': layer, 'context': context,
                'generation': generation, 'production_roots': args.production_root, 'entries': entries}
    restored = root / '.lake/ci-cache' / (layer + '.json')
    try:
        old = json.loads(restored.read_text())
    except (OSError, ValueError):
        old = {}
    changed = old.get('context') != context or old.get('generation') != generation
    target = args.output
    target.parent.mkdir(parents=True, exist_ok=True)
    if not changed and target.is_file() and old.get('archive_sha256') == file_hash(target):
        # This exact archive was fully validated during restore. Ignore changed
        # mtimes in compatibility; identical content/modes need no recompression.
        retained = {k: v for k, v in old.items() if k != 'archive_sha256'}
        write_json(args.metadata or Path(str(target) + '.json'), retained)
        emit({'generation': generation, 'context': context, 'changed': False,
              'bytes': target.stat().st_size, 'files': len(entries), 'archive': str(target),
              'reused_archive': True}, args.github_output)
        return
    temporary = target.with_name('partial-' + target.name)
    try:
        with archive_stream(temporary, True) as stream, tarfile.open(fileobj=stream, mode='w|') as archive:
            content = (json.dumps(metadata, sort_keys=True) + '\n').encode()
            header = tarfile.TarInfo('checkpoint.json')
            header.size = len(content)
            header.mode = 0o644
            archive.addfile(header, io.BytesIO(content))
            for entry in entries:
                base = root if entry['area'] == 'workspace' else native
                path = contained(base, entry['path'])
                if semantic(info(base, path, entry['area'])) != semantic(entry):
                    raise ValueError('generated output changed before archive copy')
                header = tarfile.TarInfo('payload/' + entry['area'] + '/' + entry['path'])
                header.size, header.mode = entry['size'], entry['mode']
                header.mtime = entry['mtime_ns'] / 1_000_000_000
                with path.open('rb') as source:
                    archive.addfile(header, source)
                if semantic(info(base, path, entry['area'])) != semantic(entry):
                    raise ValueError('generated output changed during archive copy')
        os.replace(temporary, target)
    finally:
        temporary.unlink(missing_ok=True)
    write_json(args.metadata or Path(str(target) + '.json'), metadata)
    emit({'generation': generation, 'context': context, 'changed': changed,
          'bytes': target.stat().st_size, 'files': len(entries), 'archive': str(target)}, args.github_output)


def validate_metadata(data, args):
    if data.get('schema') != SCHEMA or data.get('layer') != args.layer:
        raise ValueError('unsupported checkpoint schema/layer')
    if data.get('context') != contexts(args.root)[args.layer + '_context']:
        raise ValueError('incompatible checkpoint context')
    entries = data.get('entries')
    if not isinstance(entries, list) or data.get('generation') != digest([semantic(e) for e in entries]):
        raise ValueError('invalid checkpoint generation')
    scopes = allowed_scopes(args.root, args.layer, args.native_cache)
    names = set()
    for e in entries:
        if e.get('area') not in ('workspace', 'native') or type(e.get('size')) is not int or e['size'] < 0:
            raise ValueError('invalid checkpoint entry')
        if type(e.get('mode')) is not int or not 0 <= e['mode'] <= 0o777:
            raise ValueError('invalid checkpoint mode')
        if type(e.get('mtime_ns')) is not int or e['mtime_ns'] < 0 or \
                not re.fullmatch('[0-9a-f]{64}', str(e.get('sha256'))):
            raise ValueError('invalid checkpoint identity')
        key = (e['area'], e['path'])
        if key in names:
            raise ValueError('duplicate checkpoint entry')
        names.add(key)
        base = args.root if e['area'] == 'workspace' else args.native_cache
        path = contained(base, e['path'])
        if not any(area == e['area'] and (path == scope or path.is_relative_to(scope))
                   for area, scope in scopes):
            raise ValueError('checkpoint entry outside generated scopes')
    return entries


def restore(args):
    """Validate the entire archive before any overlay; atomically replace files.

    No tar extraction API is used. Copies break old cache hardlinks before writes,
    preserving other workspaces' immutable artifact bytes and source permissions.
    """
    metadata = None
    for applying in (False, True):
        with archive_stream(args.input, False) as stream, tarfile.open(fileobj=stream, mode='r|') as archive:
            members = iter(archive)
            header = next(members, None)
            if header is None or header.name != 'checkpoint.json' or not header.isreg() or header.size > 256 * 1024**2:
                raise ValueError('missing/oversized checkpoint manifest')
            current = json.loads(archive.extractfile(header).read())
            entries = validate_metadata(current, args)
            if metadata is not None and current != metadata:
                raise ValueError('archive manifest changed during restore')
            metadata = current
            for entry in entries:
                member = next(members, None)
                expected = 'payload/' + entry['area'] + '/' + entry['path']
                if member is None or not member.isreg() or member.name != expected or member.size != entry['size']:
                    raise ValueError('missing, nonregular or unexpected checkpoint member')
                source = archive.extractfile(member)
                hasher = hashlib.sha256()
                temporary = None
                target = None
                try:
                    if applying:
                        base = args.root if entry['area'] == 'workspace' else args.native_cache
                        target = contained(base, entry['path'])
                        target.parent.mkdir(parents=True, exist_ok=True)
                        fd, name = tempfile.mkstemp(prefix='.checkpoint-', dir=target.parent)
                        temporary = Path(name)
                        output = os.fdopen(fd, 'wb')
                    else:
                        output = None
                    try:
                        while chunk := source.read(1024 * 1024):
                            hasher.update(chunk)
                            if output:
                                output.write(chunk)
                    finally:
                        if output:
                            output.close()
                    if hasher.hexdigest() != entry['sha256']:
                        raise ValueError('checkpoint content hash mismatch')
                    if applying:
                        os.chmod(temporary, entry['mode'])
                        os.utime(temporary, ns=(entry['mtime_ns'], entry['mtime_ns']))
                        os.replace(temporary, target)
                finally:
                    if temporary:
                        temporary.unlink(missing_ok=True)
            if next(members, None) is not None:
                raise ValueError('unexpected extra checkpoint member')
    write_json(args.root / '.lake/ci-cache' / (args.layer + '.json'),
               dict(metadata, archive_sha256=file_hash(args.input)))
    if args.metadata:
        write_json(args.metadata, metadata)
    emit({'layer': args.layer, 'generation': metadata['generation'],
          'files': len(metadata['entries']), 'restored': True}, args.github_output)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ('context', 'pack', 'restore'):
        p = sub.add_parser(name)
        p.add_argument('--root', type=Path, default=Path.cwd())
        p.add_argument('--native-cache', type=Path)
        p.add_argument('--github-output', type=Path)
        if name != 'context':
            p.add_argument('--layer', choices=LAYERS, required=True)
            p.add_argument('--metadata', type=Path)
        if name == 'pack':
            p.add_argument('--output', type=Path, required=True)
            p.add_argument('--production-root', action='append', default=[])
        if name == 'restore':
            p.add_argument('--input', type=Path, required=True)
    args = parser.parse_args(argv)
    args.root = args.root.absolute()
    args.native_cache = (args.native_cache or Path(os.environ.get('LAKE_CACHE_DIR', args.root / '.lake/native-cache'))).absolute()
    try:
        if args.action == 'context':
            emit(contexts(args.root), args.github_output)
        elif args.action == 'pack':
            pack(args)
        else:
            restore(args)
        return 0
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        print('Checkpoint failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
