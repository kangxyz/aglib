"""Exact dependency impact from immutable pinned Git source/import snapshots.

Selection performs no network, Lean invocation or worktree reads. The explicit
planning recovery function obtains missing Git objects only; existing dependency
worktrees, their HEADs and their dirty bytes are never changed or trusted.
"""
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tomllib
from urllib.parse import urlsplit

from .configuration import _lake_name, read_config_spec, source_module_name
from .source import lean_imports

TOOLCHAIN = {'Lean', 'Init', 'Std', 'Lake'}


class _PinnedObjectsMissing(ValueError):
    pass


class DependencySourcesUnavailable(ValueError):
    def __init__(self, workspace, path, dependency, revision=None, reason=None):
        self.workspace, self.path, self.dependency = workspace, path, dependency
        self.revision, self.reason = revision, reason
        super().__init__('Pinned dependency sources unavailable: ' + str(dependency)
                         + (f' at {revision}' if revision else '')
                         + (': ' + reason if reason else ''))


def _env():
    value = dict(os.environ, GIT_NO_REPLACE_OBJECTS='1', GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
    for key in ('GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_OBJECT_DIRECTORY',
                'GIT_ALTERNATE_OBJECT_DIRECTORIES'):
        value.pop(key, None)
    return value


def _git(directory, *args, input=None):
    return subprocess.run(['git', *args], cwd=directory, env=_env(), input=input,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def _checked(directory, *args, input=None):
    result = _git(directory, *args, input=input)
    if result.returncode:
        raise ValueError('Dependency Git command failed (' + ' '.join(args) + '): '
                         + result.stderr.decode(errors='replace').strip())
    return result.stdout


def _relative(value, label):
    if not isinstance(value, str) or not value or '\\' in value:
        raise ValueError('Invalid ' + label)
    path = PurePosixPath(value)
    if path.is_absolute() or '..' in path.parts or path.as_posix() != value:
        raise ValueError('Escaping/noncanonical ' + label + ': ' + value)
    return path


def _pins(pins):
    result = {}
    for pin in pins.values() if isinstance(pins, dict) else pins:
        name = _lake_name(pin.get('name', ''))
        if not name or name in {'.', '..'} or '/' in name or '\\' in name or name in result:
            raise ValueError('Invalid/duplicate dependency package: ' + name)
        if pin.get('type') == 'path':
            # The configured client parent is a local graph, not a Git package.
            continue
        if pin.get('type') != 'git' or re.fullmatch('[0-9a-f]{40}', pin.get('rev', '')) is None:
            raise ValueError('Dependency sources require full pinned Git commits: ' + name)
        _relative(pin.get('subDir') or '.', 'dependency subDir')
        result[name] = pin
    return result


def _validate_path_pins(root, config, workspace, pins):
    parent = next(w for w in config['workspaces'] if w['id'] == 'root')
    for pin in pins.values() if isinstance(pins, dict) else pins:
        if pin.get('type') != 'path':
            continue
        directory = pin.get('dir')
        if (workspace['id'] == 'root' or not isinstance(directory, str)
                or _lake_name(pin.get('name', '')) != _lake_name(parent.get('package', ''))
                or (root / workspace['path'] / directory).resolve() != (root / config['package_dir']).resolve()):
            raise DependencySourcesUnavailable(workspace['id'], workspace['path'], pin.get('name'),
                                               reason='path dependency is not the exact configured parent')


def _package_path(root, config, workspace, name):
    relative = _relative(workspace['path'], 'workspace path')
    candidates = [root / relative / '.lake/packages' / name]
    parent = root / _relative(config['package_dir'], 'package path') / '.lake/packages' / name
    if parent not in candidates:
        candidates.append(parent)
    # Clients share their parent's pin store before their .lake link exists.
    for candidate in candidates:
        if not candidate.resolve().is_relative_to(root.resolve()):
            raise ValueError('Dependency package path escapes checkout: ' + str(candidate))
        if candidate.exists():
            return candidate
    return candidates[-1]


def _repository(path):
    if not path.is_dir():
        return False
    result = _git(path, 'rev-parse', '--show-toplevel')
    if result.returncode or Path(result.stdout.decode().strip()).resolve() != path.resolve():
        raise ValueError('Existing dependency path is not its own Git worktree: ' + str(path))
    return True


def _objects(root, config, workspace, name, pin):
    path = _package_path(root, config, workspace, name)
    if not _repository(path):
        raise DependencySourcesUnavailable(workspace['id'], workspace['path'], name, pin['rev'], 'missing checkout')
    result = _git(path, 'rev-parse', '--verify', pin['rev'] + '^{commit}')
    if result.returncode:
        raise DependencySourcesUnavailable(workspace['id'], workspace['path'], name, pin['rev'], 'missing commit object')
    if result.stdout.decode().strip() != pin['rev']:
        raise ValueError('Dependency pin is not a commit object: ' + name)
    return path


def _blobs(repository, revision, paths):
    if not paths:
        return {}
    output = _checked(repository, 'cat-file', '--batch',
                      input=''.join(revision + ':' + p + '\n' for p in paths).encode())
    stream, values = io.BytesIO(output), {}
    for path in paths:
        header = stream.readline().split()
        if len(header) != 3 or header[1] != b'blob':
            raise _PinnedObjectsMissing('Unavailable pinned source blob: ' + path)
        values[path] = stream.read(int(header[2])).decode()
        if stream.read(1) != b'\n':
            raise ValueError('Truncated pinned source blob: ' + path)
    return values


def _source_index(repository, pin):
    revision = pin['rev']
    entries = {}
    tree = _git(repository, 'ls-tree', '-rz', revision)
    if tree.returncode:
        raise _PinnedObjectsMissing('Unavailable pinned source tree: ' + revision)
    for item in tree.stdout.split(b'\0'):
        if not item:
            continue
        metadata, path = item.split(b'\t', 1)
        mode, kind, _ = metadata.split()
        decoded = path.decode()
        if '\n' in decoded or '\r' in decoded:
            raise ValueError('Noncanonical pinned Git source path')
        entries[decoded] = (mode, kind)
    subdir = _relative(pin.get('subDir') or '.', 'dependency subDir')
    lake = (subdir / 'lakefile.toml').as_posix()
    lean_lake = (subdir / 'lakefile.lean').as_posix()
    if lake in entries:
        data = tomllib.loads(_blobs(repository, revision, [lake])[lake])
        roots = {subdir / _relative(data.get('srcDir', '.'), 'dependency srcDir')}
        for kind in ('lean_lib', 'lean_exe'):
            roots.update(subdir / _relative(row.get('srcDir', data.get('srcDir', '.')), 'dependency srcDir')
                         for row in data.get(kind, []))
    elif lean_lake in entries:
        # Exact conventional source paths, never guessed package namespaces.
        roots = {subdir}
    else:
        raise ValueError('Pinned dependency has no Lake configuration: ' + pin['name'])
    modules = {}
    for path, (mode, kind) in entries.items():
        source = PurePosixPath(path)
        if source.suffix != '.lean' or source.name == 'lakefile.lean' or any(p in {'.lake', '.git'} for p in source.parts):
            continue
        for prefix in roots:
            if not source.is_relative_to(prefix):
                continue
            if mode == b'120000' or kind != b'blob':
                raise ValueError('Pinned Lean source must be a regular blob: ' + path)
            module = source_module_name(Path(source.relative_to(prefix)))
            if module in modules and modules[module] != path:
                raise ValueError('Ambiguous pinned source module: ' + module)
            modules[module] = path
    if not modules:
        raise ValueError('Pinned dependency has no usable Lean source modules: ' + pin['name'])
    return modules


class _Phase:
    def __init__(self, root, config, workspace, pins, indices, imports):
        self.indices, self.imports, self.keys = {}, imports, {}
        _validate_path_pins(root, config, workspace, pins)
        for name, pin in _pins(pins).items():
            repository = _objects(root, config, workspace, name, pin)
            key = (str(repository.resolve()), pin['rev'], pin.get('subDir') or '.')
            if key not in indices:
                try:
                    indices[key] = _source_index(repository, pin)
                except _PinnedObjectsMissing as error:
                    raise DependencySourcesUnavailable(workspace['id'], workspace['path'], name, pin['rev'], str(error)) from error
            self.indices[name] = (repository, pin, indices[key])
            self.keys[name] = key
        self.workspace = workspace

    def owners(self, module):
        return [name for name, (_, _, modules) in self.indices.items() if module in modules]

    def resolve(self, module):
        matches = self.owners(module)
        if len(matches) != 1:
            raise DependencySourcesUnavailable(self.workspace['id'], self.workspace['path'], module,
                                               reason='missing or ambiguous exact pinned module owner')
        owner = matches[0]
        key = self.keys[owner]
        if key not in self.imports:
            repository, pin, modules = self.indices[owner]
            try:
                blobs = _blobs(repository, pin['rev'], sorted(set(modules.values())))
            except _PinnedObjectsMissing as error:
                raise DependencySourcesUnavailable(self.workspace['id'], self.workspace['path'], owner, pin['rev'], str(error)) from error
            self.imports[key] = {name: lean_imports(blobs[path]) for name, path in modules.items()}
        return owner, self.imports[key][module]


def affected_origins(root, config, workspace, base, current, old, changed_deps, old_pins, new_pins):
    """Return narrow local/client keys affected by old/current external ownership.

    Root pin changes apply to every configured client's direct external imports,
    including clients whose inherited manifest bytes did not change. Removed old
    local identities remain seeds for the caller's existing reverse-union pass.
    ``base`` binds the supplied old local snapshot/pins; no history is inferred.
    """
    del base
    root = Path(root).resolve()
    changed = {_lake_name(name) for name in changed_deps}
    if not changed:
        return set()
    reverse, seeds = {}, set()
    indices, imports = {}, {}
    prior = _Phase(root, config, workspace, old_pins, indices, imports)
    present = _Phase(root, config, workspace, new_pins, indices, imports)
    for label, records, phase in (('old', old, prior), ('current', current, present)):
        pending = [(key, row['imports']) for key, row in records.items()]
        seen = set()
        while pending:
            consumer, imports = pending.pop()
            if consumer in seen:
                continue
            seen.add(consumer)
            for imported in imports:
                if imported in records:
                    provider = imported
                elif imported.split('.')[0] in TOOLCHAIN:
                    continue
                else:
                    owners = phase.owners(imported)
                    removed = label == 'current' and not owners and len(prior.owners(imported)) == 1 and prior.owners(imported)[0] in changed
                    if removed:
                        # A current stale import of an actually removed old
                        # provider is still affected; compilation may diagnose
                        # the broken import after the planner preserves its key.
                        owner, dependencies = prior.owners(imported)[0], []
                        provider = ('old', owner, imported)
                    elif len(owners) == 1 and owners[0] in changed:
                        # Exact ownership is enough: every consumer of a changed
                        # provider is affected. Do not parse that dependency's
                        # potentially huge mathematical bodies just to seed it.
                        owner, dependencies = owners[0], []
                        provider = (label, owner, imported)
                    else:
                        owner, dependencies = phase.resolve(imported)
                        provider = (label, owner, imported)
                    if owner in changed:
                        seeds.add(provider)
                    pending.append((provider, dependencies))
                reverse.setdefault(provider, set()).add(consumer)
    reached, pending = set(seeds), list(seeds)
    while pending:
        for node in reverse.get(pending.pop(), set()) - reached:
            reached.add(node); pending.append(node)
    return {key for key in reached if isinstance(key, str) and key in (current.keys() | old.keys())
            and (workspace['id'] == 'root' or (current.get(key) or old[key])['workspace'] == workspace['id'])}


def _url(value, allow_local):
    if not isinstance(value, str) or not value or any(c.isspace() for c in value):
        raise ValueError('Invalid dependency source URL')
    parts = urlsplit(value)
    if (parts.scheme == 'https' and parts.hostname and not parts.username and not parts.password
            and not parts.query and not parts.fragment and parts.path not in {'', '/'}
            and '..' not in PurePosixPath(parts.path).parts):
        return value
    if allow_local and (Path(value).is_absolute() or parts.scheme == 'file'):
        return value
    raise ValueError('Dependency acquisition requires a noninteractive HTTPS repository URL')


def _manifest(root, path, revision=None):
    name = (_relative(path, 'workspace path') / 'lake-manifest.json').as_posix()
    if revision:
        exists = _git(root, 'cat-file', '-e', revision + ':' + name)
        if exists.returncode:
            return None
        return json.loads(_checked(root, 'show', revision + ':' + name))
    source = root / name
    return json.loads(source.read_text()) if source.is_file() else None


def _historical_coordinates(root, config, base):
    path = config['config_path']
    entry = _checked(root, 'ls-tree', '-z', base, '--', path)
    if not entry:
        return {w['id']: w['path'] for w in config['workspaces']}
    prior = read_config_spec(_checked(root, 'show', base + ':' + path).decode(), path)
    return {'root': prior['package_dir'], **{c['id']: c['path'] for c in prior['clients']}}


def _sources_present(repository, pin):
    try:
        modules = _source_index(repository, pin)
    except _PinnedObjectsMissing:
        return False
    descriptions = _checked(repository, 'cat-file', '--batch-check', input=''.join(
        pin['rev'] + ':' + path + '\n' for path in sorted(set(modules.values()))).encode())
    return all(len(line.split()) == 3 and line.split()[1] == b'blob'
               for line in descriptions.splitlines())


def resolve_planning_sources(root, config, base, *, workspace=None, old_pins=None,
                             new_pins=None, dependencies=None, allow_local=False):
    """Explicit source-only recovery for an authoritative planning retry.

    Fetch exact old/current commit objects; create absent package worktrees at
    their current pin. Existing worktree HEADs, index and source bytes stay intact.
    URL/access/revision failures are errors, never evidence of no dependency effect.
    """
    root = Path(root).resolve()
    if workspace is None:
        workspaces = config['workspaces']
    else:
        workspaces = [workspace]
    coordinates = _historical_coordinates(root, config, base) if old_pins is None else {}
    requests = []
    for item in workspaces:
        before_path = coordinates.get(item['id'], item['path'])
        before = old_pins if old_pins is not None else (_manifest(root, before_path, base) or {}).get('packages')
        after = new_pins if new_pins is not None else (_manifest(root, item['path']) or {}).get('packages')
        # Clients inherit the configured parent pins even before preparation
        # materializes their generated manifest; no namespace guess is involved.
        if item['id'] != 'root':
            if before is None:
                before = (_manifest(root, coordinates.get('root', config['package_dir']), base) or {}).get('packages')
            if after is None:
                after = (_manifest(root, config['package_dir']) or {}).get('packages')
        if before is None or after is None:
            raise DependencySourcesUnavailable(item['id'], item['path'], 'manifest', reason='missing exact old/current manifest')
        # Client inherited manifests may contain one local parent. It is never
        # silently treated as an external Git dependency or an arbitrary path.
        _validate_path_pins(root, config, item, after)
        prior, present = _pins(before), _pins(after)
        for name in sorted(prior.keys() | present.keys()):
            if dependencies is not None and name not in dependencies:
                continue
            for pin in (prior.get(name), present.get(name)):
                if pin is not None:
                    requests.append((item, name, pin, present.get(name)))
    fetched, created, seen = [], set(), set()
    for item, name, pin, current in requests:
        path = _package_path(root, config, item, name)
        identity = (str(path), pin['rev'])
        url = _url(pin.get('url'), allow_local)
        if identity in seen:
            continue
        seen.add(identity)
        if not path.exists():
            origin = _url((current or pin).get('url'), allow_local)
            parent = path.parent
            parent.mkdir(parents=True, exist_ok=True)
            if not parent.resolve().is_relative_to(root):
                raise ValueError('Dependency acquisition path escapes checkout')
            _checked(parent, 'init', str(path))
            # Lake checks origin when resolving later pin updates. Bind a new
            # checkout to its current source even when fetching old objects first,
            # so Lake can preserve its build cache instead of replacing the tree.
            _checked(path, 'remote', 'add', 'origin', origin)
            created.add(path)
        _repository(path)
        available = _git(path, 'rev-parse', '--verify', pin['rev'] + '^{commit}')
        if available.returncode or not _sources_present(path, pin):
            refetch = ['--refetch'] if available.returncode == 0 else []
            _checked(path, 'fetch', '--no-tags', '--no-recurse-submodules', '--no-write-fetch-head', *refetch, url, pin['rev'])
            _objects(root, config, item, name, pin)
            if not _sources_present(path, pin):
                raise ValueError('Exact pinned source objects remain unavailable after acquisition: ' + name)
            fetched.append({'workspace': item['id'], 'dependency': name, 'revision': pin['rev']})
        if path in created and current is not None and pin['rev'] == current['rev']:
            _checked(path, '-c', 'advice.detachedHead=false', 'checkout', '--detach', current['rev'])
    return {'status': 'sources-ready', 'fetched': fetched, 'created': sorted(str(p) for p in created),
            'coverage': 'pinned Git sources only; no Lean, artifacts or check coverage'}
