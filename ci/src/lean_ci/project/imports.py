"""Guarded declarative facade authoring using the common source renderer."""
from copy import deepcopy
import hashlib
import os
from pathlib import Path
import stat
import subprocess
import tempfile

from .configuration import lean_files, load_config
from ..checks import guards
from .source import lean_imports, module_path, uses_module_system


def _stamp(path):
    try:
        info = path.lstat()
        target = path.stat()
        fields = lambda value: (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns)
        return fields(info), fields(target), hashlib.sha256(path.read_bytes()).hexdigest()
    except FileNotFoundError:
        return None


def _head(root):
    if not (root / '.git').exists():
        return None
    result = subprocess.run(['git', 'rev-parse', '--verify', 'HEAD'], cwd=root,
                            capture_output=True, text=True, check=True)
    return result.stdout.strip()


def _snapshot(root, config):
    paths = {p.relative_to(root).as_posix() for p in lean_files(root)}
    paths.add(config['config_path'])
    for values in config['policy'].values():
        paths.update(values)
    for workspace in config['workspaces']:
        paths.update((Path(workspace['path']) / p).as_posix() for p in
                     ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'))
    components = {root}
    for value in paths:
        parent = (root / value).parent
        while parent.is_relative_to(root):
            components.add(parent)
            if parent == root:
                break
            parent = parent.parent
    identities = {}
    for directory in components:
        try:
            link, target = directory.lstat(), directory.stat()
            fields = lambda info: (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid)
            identities[str(directory)] = (fields(link), fields(target),
                (os.readlink(directory), link.st_ctime_ns) if directory.is_symlink() else None)
        except FileNotFoundError:
            identities[str(directory)] = None
    return _head(root), {p: _stamp(root / p) for p in sorted(paths)}, identities


def _virtual(config, key):
    workspace_id = next((w['id'] for w in config['workspaces'] if w['id'] != 'root' and key.startswith(w['id'] + ':')), 'root')
    name = key if workspace_id == 'root' else key[len(workspace_id) + 1:]
    workspace = next((w for w in config['workspaces'] if w['id'] == workspace_id), None)
    if workspace is None:
        raise ValueError('Generated facade has no configured workspace: ' + key)
    matches = [(declaration, d) for declaration, d in workspace['declarations'].items()
               if any(name == r or (d['submodules'] and name.startswith(r + '.')) for r in d['roots'])]
    if len(matches) != 1:
        raise ValueError('Generated facade has no unique Lake owner: ' + key)
    declaration, data = matches[0]
    role = next(r for r, names in workspace['roles'].items() if declaration in names)
    return {'module': name, 'workspace': workspace_id, 'role': role,
            'declaration': declaration,
            'path': (Path(workspace['path']) / data['src_dir'] / module_path(name)).as_posix()}


def _products(root, config):
    policy, _, _, _, _ = guards._policies(root, config)
    effective = deepcopy(config)
    texts = {key: (root / row['path']).read_text() for key, row in effective['modules'].items()}
    missing = {}
    for spec in policy.get('generated', []):
        if spec['module'] not in effective['modules']:
            missing[spec['module']] = spec
    for rule in policy.get('discover_generated', []):
        if not rule.get('top_level'):
            continue
        for row in list(effective['modules'].values()):
            parts, prefix = guards._parts(row['module']), guards._parts(rule['root'])
            if parts[:len(prefix)] != prefix or len(parts) <= len(prefix) + 1:
                continue
            family = parts[len(prefix)]
            if family in rule.get('excluded_families', []):
                continue
            name = rule['root'] + '.' + family
            key = name if row['workspace'] == 'root' else row['workspace'] + ':' + name
            if key not in effective['modules']:
                missing[key] = {'module': key, 'marker': rule.get('marker', guards.MARKER),
                                'render': rule.get('render', {})}
    for key, spec in missing.items():
        row = _virtual(effective, key)
        target = root / row['path']
        if target.exists():
            raise ValueError('Generated facade would take over an unenrolled source: ' + row['path'])
        settings = spec.get('render', spec)
        modern = settings.get('modern', True)
        if not isinstance(modern, bool):
            modern = True
        effective['modules'][key] = row
        texts[key] = settings.get('header', '') + spec.get('marker', guards.MARKER).rstrip('\n') + '\n' + ('module\n' if modern else '')
    # Existing source and prospective virtual products use the same renderer.
    _, _, outputs = guards._generated(effective, texts, policy)
    proposed = dict(texts)
    for key, row in effective['modules'].items():
        if row['path'] in outputs:
            proposed[key] = outputs[row['path']]
    errors, _, _ = guards._generated(effective, proposed, policy)
    local = {w['id']: {r['module']: k for k, r in effective['modules'].items()
                      if r['workspace'] == w['id']} for w in effective['workspaces']}
    roots = {guards._parts(r['module'])[0] for r in effective['modules'].values()}
    graph = {}
    for key, row in effective['modules'].items():
        graph[key] = set()
        for name in lean_imports(proposed[key]):
            target = local[row['workspace']].get(name, local['root'].get(name))
            if target:
                graph[key].add(target)
            elif guards._parts(name)[0] in roots:
                errors.append(row['path'] + ': unresolved local proposed import ' + name)
    errors.extend(guards._cycles(graph))
    if errors:
        raise ValueError('Invalid generated facade products: ' + '\n'.join(dict.fromkeys(errors)))
    return outputs


def maintain(root, config_path='.github/lean-ci.toml', *, write=False):
    """Validate all prospective products before guarded atomic per-file writes."""
    root = Path(root).resolve()
    config = load_config(root, config_path)
    before = _snapshot(root, config)
    if load_config(root, config_path) != config:
        raise ValueError('Import configuration changed during enrollment')
    outputs = _products(root, config)
    changed = [p for p, value in outputs.items() if not (root / p).is_file() or (root / p).read_text() != value]
    if _snapshot(root, config) != before:
        raise ValueError('Import source/policy/HEAD inputs changed before writing')
    if write:
        staged = []
        try:
            for relative in changed:
                target = root / relative
                if not target.resolve().is_relative_to(root) or target.is_symlink():
                    raise ValueError('Generated target escaped its source root')
                with tempfile.NamedTemporaryFile(dir=target.parent, prefix='.lean-ci-import-', delete=False) as output:
                    output.write(outputs[relative].encode())
                    temporary = Path(output.name)
                temporary.chmod(stat.S_IMODE(target.stat().st_mode) if target.exists() else 0o644)
                staged.append((temporary, target, _stamp(target)))
            if _snapshot(root, config) != before:
                raise ValueError('Import source/policy/HEAD inputs changed before writing')
            for temporary, target, expected in staged:
                if not target.resolve().is_relative_to(root) or target.is_symlink() or _stamp(target) != expected or _head(root) != before[0]:
                    raise ValueError('Generated output ownership/HEAD changed before replacement')
                os.replace(temporary, target)
        finally:
            for temporary, _, _ in staged:
                temporary.unlink(missing_ok=True)
    return {'generated': len(outputs), 'changed': changed, 'written': write}
