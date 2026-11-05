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
SUPPORTED_TOOLCHAIN = 'leanprover/lean4:v4.34.1'
AUDITOR_PIN = '46024e005996495c65ef609368e11ab39c4222e3'
# Explicit current public Lean configurations with default native build roots.
# These are source identities, not a parser for arbitrary executable lakefiles.
# Primary sources: leanprover-community/{mathlib4,ProofWidgets4}/blob/<rev>/lakefile.lean.
LEAN_CONFIGS = {
    ('mathlib', 'd13f23b723b8a846827a245b89c10fc7d3f11612'):
        ('https://github.com/leanprover-community/mathlib4',
         '274e720ccc7dbabeb9fbf362290dc7e5ed2c5175fbade0ef20cc19b1331affaf'),
    ('proofwidgets', '106ff4fafc74ef4ac99d81dbf3ab399118f497a5'):
        ('https://github.com/leanprover-community/ProofWidgets4',
         '0a319fffbf511dab4c3307dc105f8e8fdb4f6160020995cef5f442061cc0abca'),
}


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


def contained(base, name, checked_parents=None):
    """Check lexical containment and every leaf; memo parents only in a quiescent pass."""
    parts = relative(name).parts
    current = base
    for component in (None, *parts[:-1]):
        if component is not None:
            current /= component
        if checked_parents is None or current not in checked_parents:
            if current.is_symlink():
                raise ValueError('symlink in checkpoint path: ' + str(current))
            if checked_parents is not None:
                checked_parents.add(current)
    path = current / parts[-1]
    # Never memoize leaves: a prior regular file can be an inherited hardlink or
    # a newly introduced symlink. Atomic replacement still breaks hardlinks.
    if path.is_symlink():
        raise ValueError('symlink in checkpoint path: ' + str(path))
    return path


def configuration(root):
    import tomllib
    file = root / 'lakefile.toml'
    return tomllib.loads(file.read_text()) if file.is_file() else {}


def default_build_layout(config):
    for key, default in (('buildDir', '.lake/build'), ('leanLibDir', 'lib/lean'),
                         ('nativeLibDir', 'lib'), ('binDir', 'bin'), ('irDir', 'ir')):
        if config.get(key, default) != default:
            raise ValueError('custom generated build directory is unsupported: ' + key)


def supported(root, materialized=False):
    """Admit only the static resolution boundary this CI helper implements.

    This runs before dependency checkouts exist. Lake overrides/custom layouts
    remain on legacy transport rather than being guessed after an expensive build.
    Commands repeat this guard because an old cache may introduce an override.
    """
    root = root.absolute()
    for name in ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json',
                 'lean-toolchain', '.lake/package-overrides.json'):
        contained(root, name)
    if (root / 'lean-toolchain').read_text().strip() != SUPPORTED_TOOLCHAIN:
        raise ValueError('unsupported layered checkpoint toolchain; use legacy transport')
    if (root / 'lakefile.lean').exists() or not (root / 'lakefile.toml').is_file():
        raise ValueError('layered checkpoints require an unambiguous root lakefile.toml')
    if (root / '.lake/package-overrides.json').exists():
        raise ValueError('package-overrides.json is outside layered checkpoint resolution')
    config = configuration(root)
    default_build_layout(config)
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    if config.get('packagesDir', '.lake/packages') != '.lake/packages' or \
            manifest.get('packagesDir', '.lake/packages') != '.lake/packages' or \
            manifest.get('lakeDir', '.lake') != '.lake':
        raise ValueError('layered checkpoints require the standard .lake/packages layout')
    packages = manifest.get('packages')
    if not isinstance(packages, list):
        raise ValueError('missing resolved package list')
    names, directories = set(), set()
    for item in packages:
        if not isinstance(item, dict) or not isinstance(item.get('name'), str) or \
                not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*', item['name']):
            raise ValueError('unsupported manifest package name')
        if item['name'] in names:
            raise ValueError('duplicate manifest package name')
        names.add(item['name'])
        if item.get('subDir') is not None or item.get('configFile', 'lakefile.toml') not in \
                ('lakefile.toml', 'lakefile.lean') or \
                item.get('manifestFile', 'lake-manifest.json') != 'lake-manifest.json':
            raise ValueError('custom dependency configuration/subdirectory is unsupported')
        if item.get('type') == 'git':
            name = '.lake/packages/' + item['name']
        elif item.get('type') == 'path' and isinstance(item.get('dir'), str):
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
        config_name = item.get('configFile', 'lakefile.toml')
        config_path = path / config_name
        if config_path.is_symlink():
            raise ValueError('resolved dependency configuration is not regular')
        if config_name == 'lakefile.lean':
            known = LEAN_CONFIGS.get((item['name'], item.get('rev')))
            url = item.get('url', '').removesuffix('.git')
            if item.get('type') != 'git' or not known or url != known[0]:
                raise ValueError('arbitrary executable dependency configuration is unsupported')
            if config_path.is_file() and file_hash(config_path) != known[1]:
                raise ValueError('known dependency configuration bytes changed')
        elif (path / 'lakefile.lean').exists():
            raise ValueError('competing dependency Lean configuration is unsupported')
        elif config_path.is_file():
            import tomllib
            default_build_layout(tomllib.loads(config_path.read_text()))
        if materialized and not config_path.is_file():
            raise ValueError('resolved dependency configuration is not materialized/regular')
        # The root package, Git metadata, and nested aliases do not identify
        # independent resolved package scopes. Hyphenated leaf names are valid.
        if path == root or '.git' in path.relative_to(root).parts:
            raise ValueError('invalid resolved dependency directory')
        if any(path == previous or path.is_relative_to(previous) or previous.is_relative_to(path)
               for previous in directories):
            raise ValueError('duplicate or overlapping dependency directory')
        directories.add(path)
    return True


def dependencies(root):
    """Only resolved, repository-contained package directories are admitted."""
    supported(root)
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
    supported(root)
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
            # Lake4.34.1 regenerates this compiler input immediately before every
            # real Lean/leanir invocation (Build/Actions.lean:54–56,99–101).
            # It is neither an incremental output nor a native readiness input.
            parts = entry.parts
            if name.endswith('.setup.json') and any(
                    parts[i:i + 3] == ('.lake', 'build', 'ir') for i in range(len(parts) - 2)):
                continue
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


def stat_identity(value):
    return (value.st_dev, value.st_ino, value.st_mode, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def directory_identity(value):
    # Archive creation and ordinary reads can change directory times. Resolution
    # identity/type must stay fixed; a replaced directory/symlink is rejected.
    return value.st_dev, value.st_ino, stat.S_IFMT(value.st_mode)


def info(base, path, area, guards=None, directories=None, checked_parents=None):
    name = path.relative_to(base).as_posix()
    contained(base, name, checked_parents)
    before = path.lstat()
    value = {'area': area, 'path': name, 'size': before.st_size,
             'mode': stat.S_IMODE(before.st_mode) & 0o777,
             'mtime_ns': before.st_mtime_ns, 'sha256': file_hash(path)}
    after = path.lstat()
    if stat_identity(before) != stat_identity(after):
        raise ValueError('generated file changed during checkpoint scan: ' + name)
    if guards is not None:
        guards[(area, name)] = stat_identity(after)
    if directories is not None:
        current = path.parent
        while current.is_relative_to(base):
            if current not in directories:
                value_stat = current.lstat()
                if not stat.S_ISDIR(value_stat.st_mode):
                    raise ValueError('checkpoint directory is not regular: ' + str(current))
                directories[current] = directory_identity(value_stat)
            if current == base:
                break
            current = current.parent
    return value


def semantic(entry):
    return {k: v for k, v in entry.items() if k != 'mtime_ns'}


def snapshot(root, layer, native, production, guards=None, directories=None):
    checked_parents = set()
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
            entry = info(base, path, area, guards, directories, checked_parents)
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


class DigestingReader:
    """Hash exactly the data tarfile copies, without a separate body reread."""
    def __init__(self, source):
        self.source = source
        self.hasher = hashlib.sha256()
        self.size = 0

    def read(self, size=-1):
        data = self.source.read(size)
        self.hasher.update(data)
        self.size += len(data)
        return data


def check_directories(directories):
    for path, expected in directories.items():
        if directory_identity(path.lstat()) != expected:
            raise ValueError('generated directory changed during checkpoint copy: ' + str(path))


def pack(args):
    root, native = args.root, args.native_cache
    layer = args.layer
    guards, directories = {}, {}
    entries = snapshot(root, layer, native, args.production_root, guards, directories)
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
        check_directories(directories)
        with archive_stream(temporary, True) as stream, tarfile.open(fileobj=stream, mode='w|') as archive:
            content = (json.dumps(metadata, sort_keys=True) + '\n').encode()
            header = tarfile.TarInfo('checkpoint.json')
            header.size = len(content)
            header.mode = 0o644
            archive.addfile(header, io.BytesIO(content))
            for entry in entries:
                base = root if entry['area'] == 'workspace' else native
                # Paths were canonicalized and their directories guarded in the
                # initial scan. Copy checks are constant-time lstat/fstat guards.
                path = base / entry['path']
                expected = guards[(entry['area'], entry['path'])]
                if stat_identity(path.lstat()) != expected:
                    raise ValueError('generated output changed before archive copy')
                header = tarfile.TarInfo('payload/' + entry['area'] + '/' + entry['path'])
                header.size, header.mode = entry['size'], entry['mode']
                header.mtime = entry['mtime_ns'] / 1_000_000_000
                descriptor = os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
                with os.fdopen(descriptor, 'rb') as source:
                    if stat_identity(os.fstat(source.fileno())) != expected:
                        raise ValueError('generated output changed while opening for archive copy')
                    copied = DigestingReader(source)
                    archive.addfile(header, copied)
                    if copied.size != entry['size'] or copied.hasher.hexdigest() != entry['sha256']:
                        raise ValueError('copied checkpoint content differs from snapshot')
                    if stat_identity(os.fstat(source.fileno())) != expected:
                        raise ValueError('generated output changed during archive copy')
                if stat_identity(path.lstat()) != expected:
                    raise ValueError('generated output changed during archive copy')
        check_directories(directories)
        os.replace(temporary, target)
    finally:
        temporary.unlink(missing_ok=True)
    write_json(args.metadata or Path(str(target) + '.json'), metadata)
    emit({'generation': generation, 'context': context, 'changed': changed,
          'bytes': target.stat().st_size, 'files': len(entries), 'archive': str(target)}, args.github_output)


def validate_metadata(data, args, checked_parents=None):
    if data.get('schema') != SCHEMA or data.get('layer') != args.layer:
        raise ValueError('unsupported checkpoint schema/layer')
    if data.get('context') != contexts(args.root)[args.layer + '_context']:
        raise ValueError('incompatible checkpoint context')
    entries = data.get('entries')
    if not isinstance(entries, list) or data.get('generation') != digest([semantic(e) for e in entries]):
        raise ValueError('invalid checkpoint generation')
    scopes = set(allowed_scopes(args.root, args.layer, args.native_cache))
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
        path = contained(base, e['path'], checked_parents)
        if (e['area'], path) not in scopes and not any(
                (e['area'], parent) in scopes for parent in path.parents):
            raise ValueError('checkpoint entry outside generated scopes')
    return entries


def restore(args):
    """Validate the entire archive before any overlay; atomically replace files.

    No tar extraction API is used. Under the required quiescent/trusted CI
    boundary, parent ancestry is checked once per pass; lexical scope and each
    leaf symlink are checked for every entry. Copies break old cache hardlinks
    before writes, preserving peer artifact bytes and source permissions.
    """
    metadata = None
    for applying in (False, True):
        checked_parents = set()
        with archive_stream(args.input, False) as stream, tarfile.open(fileobj=stream, mode='r|') as archive:
            members = iter(archive)
            header = next(members, None)
            if header is None or header.name != 'checkpoint.json' or not header.isreg() or header.size > 256 * 1024**2:
                raise ValueError('missing/oversized checkpoint manifest')
            current = json.loads(archive.extractfile(header).read())
            entries = validate_metadata(current, args, checked_parents)
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
                        target = contained(base, entry['path'], checked_parents)
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
    for name in ('supported', 'context', 'pack', 'restore'):
        p = sub.add_parser(name)
        p.add_argument('--root', type=Path, default=Path.cwd())
        p.add_argument('--native-cache', type=Path)
        p.add_argument('--github-output', type=Path)
        if name == 'supported':
            p.add_argument('--materialized', action='store_true',
                           help='require every dependency config after source acquisition')
        if name in ('pack', 'restore'):
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
        supported(args.root, getattr(args, 'materialized', False))
        if args.action == 'supported':
            emit({'supported': True}, args.github_output)
        elif args.action == 'context':
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
