"""Pinned, scoped local/CI preparation without compiling mathematical targets.

Lake and Mathlib own artifact compatibility. Preparation acquires their caches,
shares only manifest-identical pinned client packages, and checks required
checker imports. A successful setup is neither compilation nor check coverage.
"""
from contextlib import contextmanager
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib

from . import build
from ..checks import native
from . import resources
from ..project.configuration import load_config
from ..project.dependencies import DependencySourcesUnavailable, resolve_planning_sources
from ..project.scope import local_base, select_scope
from ..project.source import MODULE, lean_imports, module_path

BUILD_INPUTS = ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain')
TOOLCHAIN_ROOTS = {'Lean', 'Init', 'Std', 'Lake'}


def _json(path):
    return json.loads(Path(path).read_text())


def _safe_directory(path):
    path = Path(path).absolute()
    for entry in [*reversed(path.parents), path]:
        if entry.is_symlink() or (entry.exists() and not entry.is_dir()):
            raise ValueError('Redirected/non-directory preparation output: ' + str(entry))
    return path


def _snapshot(root, config):
    paths = {root / config['config_path']}
    for workspace in config['workspaces']:
        paths.update(root / workspace['path'] / name for name in BUILD_INPUTS)
    return {str(p): p.read_bytes() if p.exists() else None for p in paths}


def _assert_pins(before):
    changed = [name for name, content in before.items()
               if (Path(name).read_bytes() if Path(name).exists() else None) != content]
    if changed:
        raise ValueError('Preparation changed pinned configuration inputs: ' + ', '.join(sorted(changed)))


def _manifest(package):
    value = _json(package / 'lake-manifest.json')
    if not isinstance(value.get('packages'), list):
        raise ValueError('A committed pinned Lake manifest is required: ' + str(package))
    names = set()
    for item in value['packages']:
        name = item.get('name')
        if not isinstance(name, str) or not name or name in names or '/' in name or '\\' in name or name in {'.', '..'}:
            raise ValueError('Invalid/duplicate manifest package identity: ' + str(name))
        names.add(name)
        if item.get('type') == 'git' and re.fullmatch('[0-9a-f]{40}', item.get('rev', '')) is None:
            raise ValueError('Dependencies require resolved full Git pins: ' + name)
    if value.get('packagesDir', '.lake/packages') != '.lake/packages':
        raise ValueError('Shared preparation requires standard .lake/packages coordinates')
    return value


def _package_name(value):
    if re.fullmatch(r'«[A-Za-z0-9_]+-[A-Za-z0-9_-]+»', value):
        return value[1:-1]
    return value


def prepare_clients(root, config, manifest):
    """Validate committed client pins before sharing this checkout's packages.

    Existing manifests are never rewritten, including byte-identical rewrites.
    Missing client manifests are materialized from the exact parent pins.
    A client may require its configured parent by path and inherit its exact
    package pins. Independently pinned or redirected package stores are errors.
    """
    package = root / config['package_dir']
    shared = _safe_directory(package / '.lake/packages')
    root_pins = {p['name']: {k: v for k, v in p.items() if k != 'inherited'}
                 for p in manifest['packages']}
    result = []
    for workspace in config['clients']:
        client = root / workspace['path']
        required = workspace['dependencies']
        if (len(required) != 1 or 'path' not in required[0]
                or _package_name(required[0].get('name', '')) != _package_name(manifest['name'])
                or (client / required[0]['path']).resolve() != package.resolve()):
            raise ValueError('Independent clients must require only their configured parent checkout: ' + workspace['id'])
        target = client / 'lake-manifest.json'
        created = False
        if not target.exists():
            current = copy.deepcopy(manifest)
            for item in current['packages']:
                item['inherited'] = True
            current['packages'].append({'type': 'path', 'name': manifest['name'], 'scope': '',
                'dir': os.path.relpath(package, client), 'inherited': False,
                'configFile': 'lakefile.toml', 'manifestFile': 'lake-manifest.json'})
            name = workspace['package']
            current['name'] = '«' + name + '»' if '-' in name else name
            current['lakeDir'] = '.lake'
            with target.open('x') as output:
                output.write(json.dumps(current, indent=2) + '\n')
            created = True
        current = _manifest(client)
        parent = [p for p in current['packages'] if p.get('type') == 'path']
        pins = {p['name']: {k: v for k, v in p.items() if k != 'inherited'}
                for p in current['packages'] if p.get('type') != 'path'}
        if (pins != root_pins or len(parent) != 1 or
                _package_name(parent[0]['name']) != _package_name(manifest['name']) or
                (client / parent[0].get('dir', '')).resolve() != package.resolve()):
            raise ValueError('Client manifest differs from parent pinned packages: ' + workspace['id'])
        cache = _safe_directory(client / '.lake')
        link = cache / 'packages'
        if link.is_symlink():
            if link.resolve() != shared.resolve():
                raise ValueError('Client packages redirect outside the pinned checkout: ' + str(link))
        elif link.exists():
            raise ValueError('Client packages must share the parent pinned package store: ' + str(link))
        else:
            cache.mkdir(parents=True, exist_ok=True)
            link.symlink_to(os.path.relpath(shared, cache), target_is_directory=True)
        result.append({'id': workspace['id'], 'path': workspace['path'], 'packages': str(shared),
                       'manifest_created': created})
    return result


def _dependency_sources(package, manifest):
    result = []
    for item in manifest['packages']:
        if item.get('type') != 'git':
            raise ValueError('Parent dependencies must be pinned Git packages: ' + item['name'])
        directory = package / '.lake/packages' / item['name']
        if not directory.is_dir():
            raise ValueError('Missing pinned dependency sources; run preparation with fetch enabled: ' + item['name'])
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
        if head != item['rev']:
            raise ValueError('Resolved dependency revision differs from committed pin: ' + item['name'])
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=normal'],
                                        cwd=directory, text=True).strip()
        if dirty:
            raise ValueError('Pinned dependency source checkout is dirty: ' + item['name'])
        source = directory / (item.get('subDir') or '.')
        roots = {source}
        lake = source / 'lakefile.toml'
        if lake.is_file():
            data = tomllib.loads(lake.read_text())
            roots.add(source / data.get('srcDir', '.'))
            for kind in ('lean_lib', 'lean_exe'):
                roots.update(source / row.get('srcDir', data.get('srcDir', '.')) for row in data.get(kind, []))
        if any(not p.resolve().is_relative_to(directory.resolve()) for p in roots):
            raise ValueError('Dependency source directory escapes pinned checkout: ' + item['name'])
        result.append((item, sorted(roots)))
    return result


def prune_obsolete_outputs(root, config):
    """Retain enrolled artifacts, pruning only stale package-owned module facets.

    Cache stamps never certify compatibility; subsequent Lake --rehash owns that
    decision. Validate every output tree before removing any stale file.
    """
    trees = []
    for workspace in config['workspaces']:
        directory = _safe_directory(root / workspace['path'] / '.lake/build')
        if directory.exists() and any(path.is_symlink() for path in directory.rglob('*')):
            raise ValueError('Symlink in package-owned build outputs: ' + str(directory))
        enrolled = {}
        for row in workspace['modules'].values():
            path = module_path(row['module']).with_suffix('')
            enrolled.setdefault(path.parent, set()).add(path.name)
        trees.append((workspace, directory, enrolled))
    result = []
    for workspace, directory, enrolled in trees:
        removed = 0
        for relative in ('lib/lean', 'ir'):
            base = directory / relative
            for path in base.rglob('*') if base.is_dir() else []:
                if path.is_file():
                    item = path.relative_to(base)
                    if not any(item.name.startswith(name + '.') for name in enrolled.get(item.parent, ())):
                        path.unlink(); removed += 1
        result.append({'workspace': workspace['id'], 'obsolete_facets_removed': removed,
                       'compatibility': 'retained; native Lake --rehash required'})
    return result


def required_imports(root, config, scope, dependencies):
    """Follow selected local/client and reachable external source imports only."""
    pending = []
    check_only = scope.get('check_only', {})
    selected = set(scope.get('modules', [])) | set(scope.get('source_style', []))
    selected.update(name for names in check_only.values() for name in names)
    for key in sorted(selected):
        if key not in config['modules']:
            raise ValueError('Preparation scope names an unavailable owned module: ' + key)
        row = config['modules'][key]
        pending.append((row['workspace'], row['module']))
    runtime, source_runtime = set(), set()
    if scope.get('declarations') or any(check_only.get(kind) for kind in ('declarations', 'axioms', 'inventory')):
        for kind in ('declarations', 'axioms', 'inventory'):
            runtime.update(native.runtime_roots(kind))
    if scope.get('common_controls') or scope.get('controls'):
        runtime.update(native.runtime_roots('controls'))
    if scope.get('source_style'):
        runtime.update(native.runtime_roots('style'))
        source_runtime.update(native.runtime_source_roots('style'))
        style_driver = next((directory / 'scripts/lint-style.lean'
                             for item, directories in dependencies if item['name'] == 'mathlib'
                             for directory in directories if (directory / 'scripts/lint-style.lean').is_file()), None)
        if style_driver is None:
            raise ValueError('Missing pinned Mathlib source style driver')
        runtime.update(lean_imports(style_driver.read_text()))
    pending.extend(('root', name) for name in sorted(runtime))
    for path in [*scope.get('expected_failure', []), *scope.get('controls', [])]:
        pending.extend(('root', name) for name in lean_imports((root / path).read_text()))
    # Mathlib's standard cache also publishes its independently pinned upstream
    # packages. Derive that set from the pinned manifest, never from a guessed
    # relation between a Lake package id and a Lean namespace.
    cache_packages = {'mathlib'}
    for item, directories in dependencies:
        if item['name'] == 'mathlib':
            manifest = next((directory / 'lake-manifest.json' for directory in directories
                             if (directory / 'lake-manifest.json').is_file()), None)
            if manifest is not None:
                cache_packages.update(p['name'] for p in _json(manifest)['packages'])
    seen, external, mathlib, packages, cache_roots = set(), set(), set(), set(), set()
    while pending:
        workspace, name = pending.pop()
        if (workspace, name) in seen:
            continue
        seen.add((workspace, name))
        if name.split('.')[0] in TOOLCHAIN_ROOTS:
            continue
        key = (workspace + ':' + name) if workspace != 'root' and workspace + ':' + name in config['modules'] else name
        local = config['modules'].get(key)
        if local is not None:
            pending.extend((local['workspace'], imported) for imported in lean_imports((root / local['path']).read_text()))
            continue
        matches = {(item['name'], directory / module_path(name))
                   for item, directories in dependencies for directory in directories
                   if (directory / module_path(name)).is_file()}
        if len(matches) != 1:
            raise ValueError('Missing/ambiguous reachable dependency source: ' + name)
        owner, source = matches.pop()
        if source.is_symlink() or not any(source.resolve().is_relative_to(directory.resolve())
                                          for item, directories in dependencies if item['name'] == owner
                                          for directory in directories):
            raise ValueError('Reachable dependency source escapes its pinned source roots: ' + name)
        external.add(name); packages.add(owner)
        if owner in cache_packages:
            cache_roots.add(name)
        if owner == 'mathlib':
            mathlib.add(name)
            # Mathlib's cache tool owns this root's transitive artifact closure.
            continue
        pending.extend(('root', imported) for imported in lean_imports(source.read_text()))
    return {'mathlib': sorted(mathlib), 'external': sorted(external), 'packages': sorted(packages),
            'cache_roots': sorted(cache_roots),
            'runtime': sorted(runtime), 'source_runtime': sorted(source_runtime),
            'basis': 'selected-source-import-closure; no coarse package fallback'}


@contextmanager
def _serialized_frontend(lean, metadata):
    """Local cache-tool bootstrap obeys the existing single-compiler admission."""
    lean = Path(lean)
    original = lean.with_name('lean-capped')
    lean.rename(original)
    lock = lean.with_name('lean.lock')
    try:
        lean.write_text('#!/usr/bin/env python3\nimport fcntl,os,subprocess,sys\n'
                       'os.environ["PATH"]=os.path.dirname(__file__)+os.pathsep+os.environ.get("PATH","")\n'
                       f'metadata={metadata!r}\n'
                       'if len(sys.argv)==2 and sys.argv[1] in metadata:\n'
                       ' sys.stdout.buffer.write(metadata[sys.argv[1]]);sys.exit(0)\n'
                       f'with open({str(lock)!r},"a") as lock:\n'
                       ' fcntl.flock(lock,fcntl.LOCK_EX)\n'
                       f' result=subprocess.run([{str(original)!r},*sys.argv[1:]])\n'
                       ' sys.exit(result.returncode if result.returncode>=0 else 128-result.returncode)\n')
        lean.chmod(0o755)
        yield
    finally:
        original.replace(lean)


def _cache_child(lean, modules, serialize):
    """Runs inside the outer owned process group, never a second scheduler."""
    if not modules:
        raise ValueError('Refusing an unscoped Mathlib cache download')
    for name in modules:
        if MODULE.fullmatch(name) is None:
            raise ValueError('Invalid scoped Mathlib cache root: ' + name)
    command = ['lake', 'exe', 'cache', 'get', *modules]
    if not serialize:
        return subprocess.call(command)
    metadata = {action: subprocess.check_output([lean, action])
                for action in ('--print-prefix', '--githash')}
    with _serialized_frontend(lean, metadata):
        return subprocess.call(command)


def _run(command, cwd, directory, label, environment, resource_config, *, cache=False):
    budget = resources.limits(environment, config=resource_config)
    threads = build.build_threads(environment, resource_config)
    budget['native_build_threads'] = threads
    with build.capped_toolchain(cwd, threads=threads, environment=environment, config=resource_config) as env:
        # Subcommands use this already loaded common distribution even when the
        # package cwd is nested (e.g. repository/lean) or PYTHONPATH was relative.
        env['PYTHONPATH'] = str(Path(__file__).resolve().parents[2]) + os.pathsep + env.get('PYTHONPATH', '')
        if cache:
            # Only our temporary local wrapper is mutable. Parent-admitted remote
            # wrappers and their high concurrency remain untouched.
            serialize = not bool(budget.get('remote_profile'))
            command = [sys.executable, '-P', '-m', 'lean_ci.execution.prepare', '--cache-child', env['LEAN'],
                       'serialized' if serialize else 'managed', *command]
        with (directory / (label + '.log')).open('x') as output:
            code = resources.run(command, cwd=cwd, env=env, budget=budget, config=resource_config,
                                 receipt=directory / (label + '.json'), stdout=output, stderr=output)
    if code:
        recovery = '; recover matching caches for the selected import closure; no cold-build fallback' if label == 'dependency-imports' else ''
        raise ValueError(f'Preparation command failed ({code}): {label}{recovery}; see {directory / (label + ".log")}')
    return {'command': command, 'receipt': str(directory / (label + '.json'))}


def _output_directory(package, directory):
    if directory is None:
        base = _safe_directory(package / '.lake/lean-ci/prepare')
        base.mkdir(parents=True, exist_ok=True)
        return Path(tempfile.mkdtemp(prefix='run-', dir=base))
    directory = _safe_directory(directory)
    directory.mkdir(parents=True, exist_ok=True)
    if any(directory.iterdir()):
        raise ValueError('Preparation requires a fresh output directory')
    return directory


def prepare(root, config_path='.github/lean-ci.toml', requested_base=None, targets=(), scope=None,
            *, environment=None, resource_config=None, directory=None, fetch=True):
    """Prepare exact selected dependencies; raise on pin drift or command failure.

    ``fetch=False`` uses already resolved sources/caches without network. The
    reusable GitHub workflow owns public native-asset restoration on hosted CI;
    local runs acquire exact-pin public assets with the same packaged transport.
    No selected subject, library, test or client target is compiled here.
    """
    root = Path(root).resolve(strict=True)
    config = load_config(root, config_path)
    before = _snapshot(root, config)
    package = root / config['package_dir']
    manifest = _manifest(package)
    _safe_directory(package / '.lake/packages')
    environment = dict(os.environ if environment is None else environment)
    resource_config = resource_config or resources.ResourceConfig()
    commands, source_recovery = [], None
    # Selection is owned by scope.py. A dependency upgrade may need exact pinned
    # sources solely to establish its namespace/import assessment. Recover those
    # on this explicit typed condition, never on an arbitrary selection error.
    if scope is None:
        try:
            scope = select_scope(root, config, base=requested_base, targets=targets)
        except DependencySourcesUnavailable:
            if not fetch:
                raise
            try:
                source_recovery = resolve_planning_sources(root, config, local_base(root, requested_base))
            finally:
                _assert_pins(before)
            scope = select_scope(root, config, base=requested_base, targets=targets)
    if not scope.get('native'):
        return {'status': 'ready', 'root': str(root), 'package_dir': config['package_dir'],
                'native': False, 'scope': scope.get('coverage'), 'commands': commands,
                'source_recovery': source_recovery,
                'coverage': 'setup-only; no compilation or checker success'}
    directory = _output_directory(package, directory)
    try:
        if fetch:
            commands.append(_run(['lake', 'resolve-deps'], package, directory, 'resolve-deps', environment, resource_config))
            _assert_pins(before)
        dependencies = _dependency_sources(package, manifest)
        clients = prepare_clients(root, config, manifest)
        for client in clients:
            if client['manifest_created']:
                path = root / client['path'] / 'lake-manifest.json'
                if before[str(path)] is not None:
                    raise ValueError('Client manifest disappeared during preparation: ' + str(path))
                # This one admitted creation has exactly the parent's committed
                # pins. Existing manifests/configuration remain immutable.
                before[str(path)] = path.read_bytes()
        outputs = prune_obsolete_outputs(root, config)
        imports = required_imports(root, config, scope, dependencies)
        repositories = sorted({match[1] for item, _ in dependencies
            if item['name'] in imports['packages'] and item['name'] != 'mathlib' and not item.get('inherited', False)
            and (match := re.fullmatch(r'https://github\.com/([^/]+/[^/]+?)(?:\.git)?/?', item.get('url', '')))})
        native_assets = 'workflow-action' if environment.get('GITHUB_ACTIONS') == 'true' else 'offline' if not fetch else 'exact-pin-public-assets'
        if repositories and fetch and native_assets != 'workflow-action':
            commands.append(_run([sys.executable, '-P', '-m', 'lean_ci.transport.cache', '--root', str(package),
                                  'restore-pinned', '--repositories', *repositories], package, directory,
                                 'native-assets', environment, resource_config))
        if imports['cache_roots'] and fetch:
            commands.append(_run(imports['cache_roots'], package, directory, 'mathlib-cache', environment, resource_config, cache=True))
        # Cache-only probing forbids an accidental broad cold build. The first
        # checker initializes its driver in a fresh, invocation-owned overlay.
        required = sorted(set(imports['external']) | {
            name for name in imports['runtime'] if name.split('.')[0] not in TOOLCHAIN_ROOTS})
        # The common style checker may compile these exact support modules in
        # its isolated overlay. Their external imports remain cache prerequisites;
        # no mathematical subject gets this source-only exception.
        required = [name for name in required if name not in imports['source_runtime']]
        if required:
            commands.append(_run(['lake', '--rehash', '--no-build', 'build',
                                  *('+' + name + ':leanArts' for name in required)], package, directory,
                                 'dependency-imports', environment, resource_config))
        result = {'status': 'ready', 'root': str(root), 'package_dir': config['package_dir'],
                  'native': True, 'scope': scope.get('coverage'),
                  'source_recovery': source_recovery,
                  'directory': str(directory), 'imports': imports, 'clients': clients,
                  'project_outputs': outputs,
                  'native_assets': native_assets, 'commands': commands,
                  'pins': {name: hashlib.sha256(content).hexdigest() for name, content in before.items() if content is not None},
                  'runtime': 'dependencies-ready; driver initialized by first native checker in its owned overlay',
                  'coverage': 'setup-only; no mathematical compilation or checker success'}
        return result
    finally:
        _assert_pins(before)


if __name__ == '__main__':
    if len(sys.argv) < 5 or sys.argv[1] != '--cache-child' or sys.argv[3] not in ('serialized', 'managed'):
        raise SystemExit('Use the public lean-ci prepare command')
    raise SystemExit(_cache_child(sys.argv[2], sys.argv[4:], sys.argv[3] == 'serialized'))
