"""Strict declarative enrollment for the mandatory common Lean CI profile."""
from pathlib import Path, PurePosixPath
import os
import json
import re
import tomllib

from .source import IDENT, MODULE, module_path

SCHEMA = 1
ROLES = ('production', 'tests', 'support', 'examples', 'diagnostics')
POLICIES = ('exceptions', 'axioms', 'budget', 'style', 'inventory', 'private_generated', 'controls', 'dependencies', 'nolints')
PIN = 'leanprover/lean4:v4.34.1'


def _keys(value, allowed, label):
    if not isinstance(value, dict) or set(value) - set(allowed):
        raise ValueError('Unknown or malformed ' + label + ' keys: ' + str(set(value) - set(allowed) if isinstance(value, dict) else value))


def _strings(value, label):
    if not isinstance(value, list) or any(not isinstance(v, str) or not v for v in value) or len(set(value)) != len(value):
        raise ValueError(label + ' must contain unique nonempty strings')
    return list(value)


def safe_path(root, value, *, exists=False):
    """Keep config coordinates portable and reject lexical and symlink escapes."""
    if not isinstance(value, str) or not value or '\\' in value:
        raise ValueError('Invalid repository path: ' + str(value))
    p = PurePosixPath(value)
    if p.is_absolute() or '..' in p.parts or p.as_posix() != value:
        raise ValueError('Noncanonical/escaping repository path: ' + value)
    result = Path(root) / value
    if not result.resolve().is_relative_to(Path(root).resolve()):
        raise ValueError('Symlink escaped repository: ' + value)
    if exists and not result.exists():
        raise ValueError('Missing configured input: ' + value)
    return result


def lean_files(root):
    """Source enrollment includes untracked additions, but never Lake/Git caches."""
    root = Path(root)
    result = []
    for directory, children, files in os.walk(root, followlinks=False):
        children[:] = sorted(c for c in children if c not in {'.git', '.lake', '__pycache__'})
        for child in children:
            path = Path(directory) / child
            if path.is_symlink():
                raise ValueError('Symlink source directory cannot establish enrollment: ' + str(path))
        for name in sorted(files):
            if name.endswith('.lean') and name != 'lakefile.lean':
                path = Path(directory) / name
                if path.is_symlink():
                    raise ValueError('Symlink Lean source cannot establish enrollment: ' + str(path))
                result.append(path)
    return result


def _roles(value, label, extra=()):
    roles = (*ROLES, *extra)
    _keys(value, roles, label)
    return {role: _strings(value.get(role, []), label + '.' + role) for role in roles}


def source_module_name(path):
    parts = Path(path).with_suffix('').parts
    if any('»' in p or '\n' in p or '\r' in p for p in parts):
        raise ValueError('Unrepresentable Lean source path: ' + str(path))
    return '.'.join(p if re.fullmatch(IDENT, p) else '«' + p + '»' for p in parts)


def _lake_name(name):
    return name[1:-1] if isinstance(name, str) and name.startswith('«') and name.endswith('»') else name


def _workspace(root, path, roles, identifier, excluded):
    package = safe_path(root, path, exists=True)
    if (package / 'lakefile.lean').exists():
        raise ValueError('Declarative CI requires lakefile.toml; lakefile.lean shadows it: ' + path)
    if package.is_symlink():
        raise ValueError('Workspace package directory cannot be a symlink: ' + path)
    for name in ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json'):
        safe_path(root, (Path(path) / name).as_posix())
    lake = tomllib.loads((package / 'lakefile.toml').read_text())
    pin = (package / 'lean-toolchain').read_text().strip()
    if pin != PIN:
        raise ValueError('Common CI requires pinned Lean 4.34.1: ' + path)
    declared_names = [d.get('name') for k in ('lean_lib', 'lean_exe') for d in lake.get(k, [])]
    defaults = lake.get('defaultTargets', [])
    if not isinstance(defaults, list) or len(set(defaults)) != len(defaults) or set(defaults) - set(declared_names):
        raise ValueError('Lake default targets must name unique declared targets: ' + path)
    test_driver = lake.get('testDriver')
    if test_driver is not None and test_driver not in roles['tests']:
        raise ValueError('Lake testDriver must belong to positive Tests: ' + path)
    requirements = lake.get('require', [])
    if len({d.get('name') for d in requirements}) != len(requirements):
        raise ValueError('Duplicate dependency declaration: ' + path)
    manifest_path = package / 'lake-manifest.json'
    for requirement in requirements:
        if 'path' in requirement and not (package / requirement['path']).resolve().is_relative_to(Path(root).resolve()):
            raise ValueError('Local dependency escapes repository: ' + str(requirement.get('name')))
    if any('git' in d for d in requirements) and not manifest_path.is_file():
        raise ValueError('Pinned dependencies require a resolved Lake manifest: ' + path)
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text())
        pins = manifest.get('packages', [])
        if not isinstance(pins, list) or len({_lake_name(d.get('name')) for d in pins}) != len(pins):
            raise ValueError('Duplicate or malformed manifest packages: ' + path)
        by_name = {_lake_name(d['name']): d for d in pins}
        for pin_data in pins:
            if pin_data.get('type') == 'git' and re.fullmatch('[0-9a-f]{40}', pin_data.get('rev', '')) is None:
                raise ValueError('Manifest Git dependencies require exact revisions: ' + pin_data['name'])
            if pin_data.get('type') not in {'git', 'path'}:
                raise ValueError('Unsupported manifest dependency type: ' + str(pin_data.get('type')))
        for requirement in requirements:
            name = requirement.get('name')
            if 'git' in requirement:
                revision = requirement.get('rev', '')
                pin_data = by_name.get(name, {})
                if (re.fullmatch('[0-9a-f]{40}', revision) is None or pin_data.get('type') != 'git'
                        or pin_data.get('rev') != revision or pin_data.get('inputRev') != revision
                        or pin_data.get('url') != requirement['git'] or pin_data.get('inherited') is not False):
                    raise ValueError('Direct dependency configuration/manifest mismatch: ' + str(name))
            elif 'path' in requirement:
                target = (package / requirement['path']).resolve()
                if not target.is_relative_to(Path(root).resolve()):
                    raise ValueError('Local dependency escapes repository: ' + str(name))
            else:
                raise ValueError('Dependencies must declare exact Git pins or local paths: ' + str(name))
    declarations = {}
    for kind in ('lean_lib', 'lean_exe'):
        for item in lake.get(kind, []):
            name = item.get('name')
            if not isinstance(name, str) or not name or name in declarations:
                raise ValueError('Missing/duplicate Lake declaration name: ' + str(name))
            src = item.get('srcDir', lake.get('srcDir', '.'))
            safe_path(package, src, exists=True)
            roots = item.get('roots', [item.get('root', name)])
            if not isinstance(roots, list) or not roots or any(not isinstance(n, str) or MODULE.fullmatch(n) is None for n in roots):
                raise ValueError('Invalid Lake roots: ' + name)
            # Arbitrary glob semantics must never silently shrink enrollment.
            globs = item.get('globs')
            if globs is not None and globs != [n + '.+' for n in roots] and globs != roots:
                raise ValueError('Unsupported Lake globs need explicit enrollment support: ' + name)
            declarations[name] = {'kind': kind, 'src_dir': src, 'roots': roots,
                                  'submodules': kind == 'lean_lib' and globs != roots,
                                  'options': item.get('leanOptions', {})}
    owners = {}
    for role, names in roles.items():
        for name in names:
            if name not in declarations or name in owners:
                raise ValueError('Unknown or multiply owned Lake declaration: ' + name)
            owners[name] = role
    if set(owners) != set(declarations):
        raise ValueError('Unowned Lake declarations: ' + ', '.join(sorted(set(declarations) - set(owners))))
    modules, paths = {}, {}
    for source in lean_files(package):
        relative = source.relative_to(root).as_posix()
        if any(relative == x or relative.startswith(x + '/') for x in excluded):
            continue
        matches = []
        for name, declaration in declarations.items():
            src = package / declaration['src_dir']
            if not source.is_relative_to(src):
                continue
            module = source_module_name(source.relative_to(src))
            if any(module == r or (declaration['submodules'] and module.startswith(r + '.')) for r in declaration['roots']):
                matches.append((name, module))
        if len(matches) > 1:
            raise ValueError('Overlapping Lake module ownership: ' + relative)
        if matches:
            name, module = matches[0]
            if module in modules:
                raise ValueError('Shadowed module: ' + module)
            key = module if identifier == 'root' else identifier + ':' + module
            row = {'module': module, 'path': relative, 'role': owners[name], 'declaration': name,
                   'workspace': identifier}
            modules[module] = row
            paths[relative] = (key, row)
    for name, declaration in declarations.items():
        if not any(row['declaration'] == name for row in modules.values()):
            raise ValueError('Lake declaration has no enrolled source: ' + name)
    return {'id': identifier, 'path': path, 'package': lake.get('name'), 'roles': roles,
            'declarations': declarations, 'options': lake.get('leanOptions', {}),
            'dependencies': lake.get('require', []), 'modules': {k: v for k, v in paths.values()}}


def _json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate configuration key: ' + key)
        result[key] = value
    return result


def read_config_spec(text, path='.github/lean-ci.toml'):
    """Normalize schema data without consulting today's source filesystem.

    Historical enrollment must use its own coordinates and policy references;
    missing historical paths are resolved in that immutable source tree.
    """
    raw = json.loads(text, object_pairs_hook=_json_object) if Path(path).suffix == '.json' else tomllib.loads(text)
    _keys(raw, {'schema', 'package_dir', 'roles', 'sources', 'clients', 'expected_failure', 'formal_only', 'controls', 'policy'}, 'configuration')
    if type(raw.get('schema')) is not int or raw['schema'] != SCHEMA:
        raise ValueError('Expected common Lean CI schema 1')
    roles = _roles(raw.get('roles', {}), 'roles')
    sources = _roles(raw.get('sources', {}), 'sources', ('references',))
    clients = []
    for client in raw.get('clients', []):
        _keys(client, {'id', 'path', 'roles'}, 'client')
        clients.append({'id': client.get('id'), 'path': client.get('path'),
                        'roles': _roles(client.get('roles', {}), 'client.roles')})
    policy = raw.get('policy', {})
    _keys(policy, POLICIES, 'policy')
    return {'schema': SCHEMA, 'package_dir': raw.get('package_dir', '.'),
            'roles': roles, 'sources': sources, 'clients': clients,
            **{kind: _strings(raw.get(kind, []), kind) for kind in ('expected_failure', 'formal_only', 'controls')},
            'policy': {kind: _strings(policy.get(kind, []), 'policy.' + kind) for kind in POLICIES}}


def load_config(root, path='.github/lean-ci.toml'):
    """Return validated JSON data; consumer code cannot supply executable policy."""
    root = Path(root).resolve()
    raw = read_config_spec(safe_path(root, path, exists=True).read_text(), path)
    package_dir = raw.get('package_dir', '.')
    safe_path(root, package_dir, exists=True)
    roles = _roles(raw.get('roles', {}), 'roles')
    if not roles['production']:
        raise ValueError('At least one production Lake declaration is required')
    sources = _roles(raw.get('sources', {}), 'sources', ('references',))
    if sources['production'] or sources['tests']:
        raise ValueError('Production and positive tests must belong to actual Lake declarations')
    source_paths = []
    for role, values in sources.items():
        for value in values:
            safe_path(root, value, exists=True)
            if any(value == x or value.startswith(x + '/') or x.startswith(value + '/') for x in source_paths):
                raise ValueError('Overlapping extra source ownership: ' + value)
            source_paths.append(value)
    clients, ids, paths = [], {'root'}, set()
    for client in raw.get('clients', []):
        _keys(client, {'id', 'path', 'roles'}, 'client')
        identifier, value = client.get('id'), client.get('path')
        if not isinstance(identifier, str) or re.fullmatch(r'[A-Za-z][\w-]*', identifier) is None or identifier in ids:
            raise ValueError('Invalid/duplicate client id: ' + str(identifier))
        safe_path(root, value, exists=True)
        if Path(package_dir).is_relative_to(Path(value)) or value in paths or any(value.startswith(p + '/') or p.startswith(value + '/') for p in paths):
            raise ValueError('Overlapping client package paths: ' + value)
        ids.add(identifier); paths.add(value)
        clients.append((identifier, value, _roles(client.get('roles', {}), 'client.roles')))
    for _, value, _ in [('root', package_dir, roles), *clients]:
        package = root / value
        lake = tomllib.loads((package / 'lakefile.toml').read_text())
        for item in [*lake.get('lean_lib', []), *lake.get('lean_exe', [])]:
            src = package / item.get('srcDir', lake.get('srcDir', '.'))
            for name in item.get('roots', [item.get('root', item['name'])]):
                owner = src / module_path(name)
                directory = owner.with_suffix('')
                for reference in sources['references']:
                    ref = root / reference
                    if owner.is_relative_to(ref) or directory.is_relative_to(ref) or ref == owner or ref.is_relative_to(directory):
                        raise ValueError('Reference ownership overlaps a Lake source root: ' + reference)
    root_workspace = _workspace(root, package_dir, roles, 'root', [v for _, v, _ in clients] + source_paths)
    workspaces = [root_workspace] + [_workspace(root, value, r, name, source_paths) for name, value, r in clients]
    modules = {name: row for workspace in workspaces for name, row in workspace['modules'].items()}
    known = {row['path'] for row in modules.values()}
    extra = []
    for role, values in sources.items():
        for value in values:
            owner = root / value
            for source in lean_files(owner) if owner.is_dir() else [owner]:
                if source.suffix != '.lean':
                    raise ValueError('Extra source owner must name Lean source: ' + value)
                relative = source.relative_to(root).as_posix()
                if relative in known:
                    raise ValueError('Duplicate source ownership: ' + relative)
                known.add(relative); extra.append({'path': relative, 'role': role})
    for workspace in workspaces:
        for source in lean_files(root / workspace['path']):
            relative = source.relative_to(root).as_posix()
            if relative not in known:
                raise ValueError('Unowned Lean source: ' + relative)
    special = {kind: _strings(raw.get(kind, []), kind)
               for kind in ('expected_failure', 'formal_only', 'controls')}
    seen_special = set()
    module_paths = {row['path'] for row in modules.values()}
    for kind, values in special.items():
        for value in values:
            safe_path(root, value, exists=True)
            if value not in known or not value.endswith('.lean') or value in seen_special:
                raise ValueError('Special role needs a uniquely enrolled exact Lean source: ' + value)
            if kind == 'controls' and value not in module_paths:
                raise ValueError('Compile-pass control requires an enrolled Lake module identity: ' + value)
            seen_special.add(value)
        for row in [*modules.values(), *extra]:
            if row['path'] in values:
                row['role'] = 'control' if kind == 'controls' else kind
    expected = special['expected_failure']
    policy = raw.get('policy', {})
    _keys(policy, POLICIES, 'policy')
    policy = {kind: _strings(policy.get(kind, []), 'policy.' + kind) for kind in POLICIES}
    for kind in ('axioms', 'private_generated'):
        if policy[kind]:
            raise ValueError('Nonempty policy.' + kind + ' is unsupported; the common axiom/private-origin predicate is fixed')
    for values in policy.values():
        for value in values:
            if not safe_path(root, value, exists=True).is_file():
                raise ValueError('Policy data must be a file: ' + value)
    return {'schema': SCHEMA, 'config_path': path, 'package_dir': package_dir,
            'roles': roles, 'sources': sources, 'clients': [w for w in workspaces if w['id'] != 'root'],
            'workspaces': workspaces, 'modules': modules, 'extra_sources': extra,
            'expected_failure': expected, 'formal_only': special['formal_only'],
            'controls': special['controls'], 'policy': policy, 'toolchain': PIN}
