"""Package-qualified incremental selection over old/current import-edge unions."""
import io
import hashlib
import json
from pathlib import Path
import subprocess
import tomllib

from .configuration import _lake_name, lean_files, load_config, read_config_spec, source_module_name
from .dependencies import DependencySourcesUnavailable, affected_origins
from .source import is_import_surface, lean_imports, module_path


BUILD_INPUTS = ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain')


def git(root, *arguments):
    result = subprocess.run(['git', *arguments], cwd=root, capture_output=True)
    if result.returncode:
        raise ValueError('Unavailable Git input (' + ' '.join(arguments) + '): ' + result.stderr.decode(errors='replace').strip())
    return result.stdout


def local_base(root, requested_base=None):
    """Local checking never asks hosted history for a baseline."""
    return git(root, 'rev-parse', '--verify', (requested_base or 'HEAD') + '^{commit}').decode().strip()


def changed_paths(root, base, head=None):
    result = git(root, 'diff', '--name-only', '-z', '--no-renames', base, *([head] if head else []))
    paths = set(filter(None, result.decode().split('\0')))
    if head is None:
        paths.update(filter(None, git(root, 'ls-files', '--others', '--exclude-standard', '-z').decode().split('\0')))
    return sorted(paths)


def _blobs(root, revision):
    names = [p for p in git(root, 'ls-tree', '-rz', '--name-only', revision).decode().split('\0')
             if p.endswith('.lean') and '.lake' not in Path(p).parts and not p.endswith('/lakefile.lean') and p != 'lakefile.lean']
    result = subprocess.run(['git', 'cat-file', '--batch'], cwd=root, capture_output=True,
                            input=''.join(revision + ':' + p + '\n' for p in names).encode())
    if result.returncode:
        raise ValueError('Unable to read old Lean snapshot: ' + revision)
    stream, values = io.BytesIO(result.stdout), {}
    for path in names:
        header = stream.readline().split()
        if len(header) != 3 or header[1] != b'blob':
            raise ValueError('Invalid old Lean blob: ' + path)
        values[path] = stream.read(int(header[2])).decode()
        if stream.read(1) != b'\n':
            raise ValueError('Truncated old Lean blob: ' + path)
    return values


def _old_lake(root, base, workspace):
    path = (Path(workspace['path']) / 'lakefile.toml').as_posix()
    exists = subprocess.run(['git', 'cat-file', '-e', base + ':' + path], cwd=root, capture_output=True)
    return tomllib.loads(git(root, 'show', base + ':' + path).decode()) if exists.returncode == 0 else {}


def _historical_bytes(root, revision, path):
    entry = git(root, 'ls-tree', '-z', revision, '--', path)
    return git(root, 'show', revision + ':' + path) if entry else None


def historical_config(root, config, revision):
    """Read old enrollment in its own immutable coordinates, without live paths."""
    content = _historical_bytes(root, revision, config['config_path'])
    if content is None:
        return None
    prior = read_config_spec(content.decode(), config['config_path'])
    prior['config_path'] = config['config_path']
    prior['workspaces'] = [{'id': 'root', 'path': prior['package_dir'], 'roles': prior['roles']},
        *[{'id': c['id'], 'path': c['path'], 'roles': c['roles']} for c in prior['clients']]]
    return prior


def snapshot(root, config, revision=None, *, enrollment=None):
    root = Path(root)
    if revision:
        text = _blobs(root, revision)
        prior = enrollment if enrollment is not None else historical_config(root, config, revision)
        workspaces = prior['workspaces'] if prior is not None else config['workspaces']
        special = {p: 'control' if kind == 'controls' else kind
            for kind in ('expected_failure', 'formal_only', 'controls') for p in (prior or {}).get(kind, [])}
    else:
        text = {row['path']: (root / row['path']).read_text() for row in config['modules'].values()}
        workspaces, prior, special = config['workspaces'], None, {}
    records = {}
    for workspace in workspaces:
        routed = prior if revision else config
        excluded = [w['path'] for w in workspaces if w['id'] != workspace['id']
                    and Path(w['path']).is_relative_to(Path(workspace['path']))]
        excluded += [owner for owners in (routed or {}).get('sources', {}).values() for owner in owners]
        if revision:
            lake = _old_lake(root, revision, workspace)
            declarations = {}
            for kind in ('lean_lib', 'lean_exe'):
                for item in lake.get(kind, []):
                    name = item['name']
                    roots = item.get('roots', [item.get('root', name)])
                    declarations[name] = {'roots': roots,
                        'src_dir': item.get('srcDir', lake.get('srcDir', '.')),
                        'submodules': kind == 'lean_lib' and item.get('globs') != roots}
        else:
            declarations = workspace['declarations']
        for path, content in text.items():
            if any(path == owner or path.startswith(owner + '/') for owner in excluded):
                continue
            source = Path(path)
            for declaration, data in declarations.items():
                prefix = Path(workspace['path']) / data['src_dir']
                if not source.is_relative_to(prefix):
                    continue
                name = source_module_name(source.relative_to(prefix))
                if not any(name == r or (data['submodules'] and name.startswith(r + '.')) for r in data['roots']):
                    continue
                key = name if workspace['id'] == 'root' else workspace['id'] + ':' + name
                if revision:
                    role = special.get(path, next((r for r, ds in workspace['roles'].items() if declaration in ds), 'unenrolled')) if prior is not None else 'unenrolled'
                else:
                    if key not in config['modules'] or config['modules'][key]['path'] != path:
                        continue
                    role = config['modules'][key]['role']
                records[key] = {'module': name, 'workspace': workspace['id'], 'path': path,
                                'role': role, 'declaration': declaration, 'package_path': workspace['path'], 'imports': lean_imports(content),
                                'facade': is_import_surface(content)}
    for record in records.values():
        prefix = '' if record['workspace'] == 'root' else record['workspace'] + ':'
        record['imports'] = [prefix + n if prefix + n in records else n for n in record['imports']]
    return records


def _enrollment_rows(config, graph, old_text=None):
    rows = {r['path']: dict(r, key=key) for key, r in graph.items()}
    if config is None:
        return rows
    if old_text is None:
        extras = config['extra_sources']
    else:
        special = {p: 'control' if kind == 'controls' else kind
            for kind in ('expected_failure', 'formal_only', 'controls') for p in config[kind]}
        extras = [{'path': p, 'role': special.get(p, role)} for role, owners in config['sources'].items()
            for p in old_text if any(p == owner or p.startswith(owner + '/') for owner in owners)]
    for row in extras:
        candidates = [w for w in config['workspaces'] if Path(row['path']).is_relative_to(Path(w['path']))]
        workspace = max(candidates, key=lambda w: len(Path(w['path']).parts)) if candidates else None
        rows[row['path']] = dict(row, key=row['path'], extra=True,
            workspace=workspace['id'] if workspace else None, package_path=workspace['path'] if workspace else None)
    return rows


def _obligations(row):
    if row is None or row['role'] in {'references', 'unenrolled'}:
        return set()
    role = row['role']
    if role in {'formal_only', 'control', 'expected_failure'}:
        return {'source', 'controls' if role == 'control' else role}
    result = {'source'}
    if not row.get('extra'):
        result.add('style')
    if not row.get('extra') and role in {'production', 'tests', 'examples', 'diagnostics'}:
        result |= {'compile', 'builtin'}
        if not row.get('facade'):
            result |= {'declarations', 'inventory'}
            if role != 'diagnostics':
                result.add('axioms')
    return result


def _enrollment_delta(current_rows, old_rows):
    result = []
    for path in sorted(current_rows.keys() | old_rows.keys()):
        before, after = old_rows.get(path), current_rows.get(path)
        fields = ('key', 'role', 'workspace', 'package_path', 'declaration', 'extra')
        if before is not None and after is not None and all(before.get(k) == after.get(k) for k in fields):
            continue
        previous, required = _obligations(before), _obligations(after)
        result.append({'path': path,
            'before': {k: before.get(k) for k in fields} if before else None,
            'after': {k: after.get(k) for k in fields} if after else None,
            'added_obligations': sorted(required - previous), 'removed_obligations': sorted(previous - required)})
    return result


def _policy_delta(root, config, prior, base):
    result = {}
    memo = {}
    for category, paths in config['policy'].items():
        before_paths = prior['policy'].get(category, []) if prior else []
        def identity(path, old):
            key = (path, old)
            if key not in memo:
                owner = Path(root) / path
                value = _historical_bytes(root, base, path) if old else owner.read_bytes()
                memo[key] = hashlib.sha256(value).hexdigest() if value is not None else None
            return [path, memo[key]]
        before = [identity(p, True) for p in before_paths] if base else []
        after = [identity(p, False) for p in paths]
        if before != after:
            result[category] = {'before': before, 'after': after}
    return result


def affected(current, old, seeds):
    selected = set(seeds)
    reverse = {}
    for graph in (old, current):
        for name, row in graph.items():
            for imported in row['imports']:
                reverse.setdefault(imported, set()).add(name)
    pending = list(selected)
    while pending:
        for name in reverse.get(pending.pop(), set()) - selected:
            selected.add(name); pending.append(name)
    return selected


def _option_identity(lake):
    return {kind: [{k: v for k, v in d.items() if k not in {'description'}} for d in lake.get(kind, [])]
            for kind in ('lean_lib', 'lean_exe')} | {'leanOptions': lake.get('leanOptions', {}), 'srcDir': lake.get('srcDir', '.')}


def _invalidations(root, config, base, changed, current, requested=(), *, old=None):
    result, seeds = [], set()
    for workspace in config['workspaces']:
        prefix = Path(workspace['path'])
        owned = {n for n, r in current.items() if r['workspace'] == workspace['id']}
        pin = (prefix / 'lean-toolchain').as_posix()
        if pin in changed:
            result.append({'path': pin, 'kind': 'toolchain', 'origins': sorted(owned)})
            seeds |= owned
        config_file = (prefix / 'lakefile.toml').as_posix()
        manifest = (prefix / 'lake-manifest.json').as_posix()
        if not {config_file, manifest}.intersection(changed):
            continue
        before = _old_lake(root, base, workspace) if base else {}
        after = tomllib.loads((Path(root) / config_file).read_text())
        package_options_changed = any(before.get(k, {}) != after.get(k, {}) for k in ('leanOptions', 'srcDir'))
        before_declarations = {d['name']: d for kind in ('lean_lib', 'lean_exe') for d in before.get(kind, [])}
        after_declarations = {d['name']: d for kind in ('lean_lib', 'lean_exe') for d in after.get(kind, [])}
        changed_declarations = {name for name in before_declarations.keys() | after_declarations.keys()
            if {k: v for k, v in before_declarations.get(name, {}).items() if k != 'description'} !=
               {k: v for k, v in after_declarations.get(name, {}).items() if k != 'description'}}
        configured_origins = owned if package_options_changed else {n for n in owned if current[n]['declaration'] in changed_declarations}
        if configured_origins:
            result.append({'path': config_file, 'kind': 'compiler-options-or-enrollment', 'origins': sorted(configured_origins)})
            seeds |= configured_origins
        old_require = {_lake_name(r['name']): r for r in before.get('require', [])}
        new_require = {_lake_name(r['name']): r for r in after.get('require', [])}
        changed_deps = {n for n in old_require.keys() | new_require.keys() if old_require.get(n) != new_require.get(n)}
        old_exists = base and subprocess.run(['git', 'cat-file', '-e', base + ':' + manifest], cwd=root, capture_output=True).returncode == 0
        old_manifest = json.loads(git(root, 'show', base + ':' + manifest)) if old_exists else {}
        owner = Path(root) / manifest
        new_manifest = json.loads(owner.read_text()) if owner.is_file() else {}
        old_pins = {_lake_name(p['name']): p for p in old_manifest.get('packages', [])}
        new_pins = {_lake_name(p['name']): p for p in new_manifest.get('packages', [])}
        if manifest in changed:
            changed_deps |= {n for n in old_pins.keys() | new_pins.keys() if old_pins.get(n) != new_pins.get(n)}
        assessed = {}
        for dep in sorted(changed_deps):
            assessment = _dependency_assessment(root, config, dep, before, after, base, workspace)
            if assessment is not None:
                if set(assessment) - current.keys():
                    raise ValueError('Dependency assessment names unavailable origins: ' + dep)
                assessed[dep] = set(assessment)
        unresolved = changed_deps - assessed.keys()
        # Explicit local targets declare partial coverage; they do not assess a
        # dependency transition or authorize a hosted native baseline.
        closure = set()
        if unresolved:
            closure = set(requested) if requested else affected_origins(
                root, config, workspace, base, current,
                old if old is not None else snapshot(root, config, base),
                unresolved, old_pins, new_pins)
        for dep in sorted(changed_deps):
            selected = assessed.get(dep, closure)
            basis = 'reviewed-assessment' if dep in assessed else 'pinned-external-import-closure'
            if requested and dep not in assessed:
                basis = 'explicit-targets; dependency-transition-unassessed'
            seeds |= selected
            result.append({'path': manifest if manifest in changed else config_file,
                           'kind': 'dependency', 'dependency': dep, 'origins': sorted(selected),
                           'before': old_pins.get(dep, {}).get('rev'),
                           'after': new_pins.get(dep, {}).get('rev'),
                           'basis': basis})
    return result, seeds


def _dependency_assessment(root, config, dependency, before, after, base, workspace):
    for path in config['policy'].get('dependencies', []):
        data = json.loads((Path(root) / path).read_text())
        pair = data.get('dependency', {})
        if pair.get('name') != dependency:
            continue
        old = next((r.get('rev') for r in before.get('require', []) if r['name'] == dependency), None)
        new = next((r.get('rev') for r in after.get('require', []) if r['name'] == dependency), None)
        if pair.get('before') == old and pair.get('after') == new and isinstance(data.get('targets'), list):
            if (set(data) != {'version', 'dependency', 'before', 'after', 'targets'} or data['version'] != 1
                    or set(pair) != {'name', 'before', 'after'} or len(set(data['targets'])) != len(data['targets'])
                    or not data['targets'] or any(not isinstance(n, str) for n in data['targets'])):
                raise ValueError('Malformed dependency assessment: ' + path)
            for side in ('before', 'after'):
                expected = data[side]
                if not isinstance(expected, dict) or set(expected) != set(BUILD_INPUTS):
                    raise ValueError('Dependency assessment must bind every package input: ' + path)
                for input_name in BUILD_INPUTS:
                    source_path = (Path(workspace['path']) / input_name).as_posix()
                    if side == 'before':
                        exists = subprocess.run(['git', 'cat-file', '-e', base + ':' + source_path], cwd=root, capture_output=True)
                        content = git(root, 'show', base + ':' + source_path) if exists.returncode == 0 else None
                    else:
                        owner = Path(root) / source_path
                        content = owner.read_bytes() if owner.is_file() else None
                    actual = hashlib.sha256(content).hexdigest() if content is not None else None
                    if expected[input_name] != actual:
                        raise ValueError('Stale dependency assessment ' + side + ' input: ' + source_path)
            return data['targets']
    return None


def select_scope(root, config=None, *, base=None, head=None, targets=(), initial=False):
    root = Path(root).resolve()
    config = config or load_config(root)
    base = base if initial else local_base(root, base)
    current = snapshot(root, config)
    prior = historical_config(root, config, base) if base else None
    old = snapshot(root, config, base, enrollment=prior) if base else {}
    old_text = _blobs(root, base) if base and prior and any(prior['sources'].values()) else {}
    current_rows = _enrollment_rows(config, current)
    old_rows = _enrollment_rows(prior, old, old_text)
    enrollment_changes = _enrollment_delta(current_rows, old_rows)
    policy_changes = _policy_delta(root, config, prior, base)
    changed = changed_paths(root, base, head) if base else sorted({r['path'] for r in current.values()} | {config['config_path']})
    by_path = {row['path']: name for graph in (old, current) for name, row in graph.items()}
    requested = []
    for value in targets:
        name = value.removeprefix('+')
        if name.endswith(':leanArts'):
            name = name[:-9]
        if name not in current:
            raise ValueError('No current owned module for target: ' + value)
        requested.append(name)
    if len(set(requested)) != len(requested):
        raise ValueError('Duplicate requested targets')
    seeds = set(current) if initial else set(requested) if targets else {by_path[p] for p in changed if p in by_path}
    invalidations, invalidated = _invalidations(root, config, base, changed, current, requested, old=old) if not initial else ([], set())
    if not targets:
        seeds |= invalidated
    if not targets:
        seeds |= {entry[side]['key'] for entry in enrollment_changes for side in ('before', 'after')
                  if entry[side] is not None and entry[side]['key'] in (current.keys() | old.keys())}
    selected = affected(current, old, seeds)
    present = selected & current.keys()
    production = {n for n in present if current[n]['role'] == 'production' and current[n]['workspace'] == 'root'}
    providers = production & seeds
    consumers = production - providers
    tests = {n for n in present if current[n]['role'] == 'tests' and current[n]['workspace'] == 'root'}
    clients = {w['id']: sorted(n for n in present if current[n]['workspace'] == w['id'] and current[n]['role'] in {'production', 'tests'})
               for w in config['clients']}
    style = {n for n in current if current[n]['path'] in changed} if not targets else set(requested)
    style = {n for n in style if current[n]['role'] not in {'formal_only', 'control', 'expected_failure'}}
    if not targets:
        style |= {entry['after']['key'] for entry in enrollment_changes if entry['after'] is not None
                  and 'style' in entry['added_obligations'] and entry['after']['key'] in current}
    source_check = set(style)
    source_eligible = {r['key'] for r in current_rows.values() if r['role'] != 'references'}
    if not targets:
        source_check |= {r['key'] for p, r in current_rows.items() if p in changed and r['key'] in source_eligible}
        source_check |= {entry['after']['key'] for entry in enrollment_changes
                         if entry['after'] is not None and entry['after']['key'] in source_eligible}
        if set(policy_changes).intersection({'style', 'exceptions', 'budget'}):
            source_check |= source_eligible
    auxiliary = {n for n in present if current[n]['role'] in {'examples', 'diagnostics'} or (current[n]['role'] == 'support' and n in requested) or (current[n]['role'] == 'formal_only' and n in requested)}
    buildable = production | tests | auxiliary | {n for names in clients.values() for n in names}
    declarations = sorted(n for n in buildable if not current[n]['facade'])
    special_changes = {entry['path'] for entry in enrollment_changes if entry['after'] is not None
                       and entry['after']['role'] in {'expected_failure', 'control'}}
    expected = sorted(p for p in config['expected_failure'] if initial or p in changed or p in special_changes or by_path.get(p) in present or 'controls' in policy_changes)
    tooling = sorted(p for p in changed if (p.startswith(('ci/', 'scripts/', '.github/')) and not p.endswith('.md') and p != config['config_path']))
    runtime_tools = {'native.py', 'text_style.py', 'runtime.py', 'application.py', 'runner.py', 'build.py', 'resources.py', 'recipe.py', 'frozen.py', 'state.py', 'batch.py', 'mappings.py', 'guards.py'}
    common_controls = initial or any((p.startswith('ci/src/lean_ci/') and (Path(p).name in runtime_tools or '/lean/' in p)) or (p.startswith('.github/workflows/') and p.endswith(('.yml', '.yaml'))) for p in tooling)
    selected_controls = sorted(p for p in config['controls'] if common_controls or p in changed or p in special_changes or by_path.get(p) in present or 'controls' in policy_changes)
    check_only = {}
    eligible = {n for n, row in current.items() if row['role'] in {'production', 'tests', 'examples', 'diagnostics'}}
    for kind, categories in {'declarations': ('nolints',), 'builtin': (),
            'axioms': (), 'inventory': ()}.items():
        touched = set(categories).intersection(policy_changes)
        origins = eligible - buildable
        if kind == 'axioms':
            origins = {n for n in origins if current[n]['role'] != 'diagnostics'}
        if kind == 'declarations':
            origins = {n for n in origins if not current[n]['facade']}
        check_only[kind] = sorted(origins) if touched and not targets else []
        if touched:
            invalidations += [{'kind': kind + '-policy', 'category': category,
                               'origins': check_only[kind], **policy_changes[category]} for category in sorted(touched)]
    return {'base': base, 'changed': changed, 'requested_targets': list(targets),
            'auxiliary': sorted(auxiliary), 'providers': sorted(providers), 'consumers': sorted(consumers), 'tests': sorted(tests),
            'clients': clients, 'modules': sorted(buildable), 'declarations': declarations,
            'source_style': sorted(style), 'style': sorted(style), 'source_check': sorted(source_check),
            'enrollment_changes': enrollment_changes, 'policy_changes': policy_changes,
            'baseline_enrollment': 'present' if prior is not None else 'absent',
            'removed': sorted(selected - current.keys()), 'expected_failure': expected,
            'controls': selected_controls,
            'common_controls': bool(common_controls), 'check_only': check_only, 'facades': sorted(n for n in present if current[n]['facade']),
            'tooling': tooling, 'invalidations': invalidations,
            'native': bool(buildable or expected or style or common_controls or any(check_only.values()) or selected_controls), 'initial': bool(initial),
            'coverage': 'current-obligation-universe' if initial else 'explicit-targets' if targets else 'affected-import-closure'}
