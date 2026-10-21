#!/usr/bin/env python3
"""Select changed Aglib providers and their affected consumers without Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from library_sources import is_import_surface, lean_imports, module_name, module_path, style_sources

ROOT = Path(__file__).resolve().parents[1]
CONFIG = {'lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json',
          'examples/downstream/lean-toolchain', 'examples/downstream/lakefile.toml',
          'examples/downstream/lakefile.lean', 'examples/downstream/lake-manifest.json'}
AUDIT = {'AglibTest.Axioms', 'AglibTest.AuditSupport'}
CONTROL_INPUTS = CONFIG | {
    '.github/workflows/ci.yml',
    'AglibTest/Axioms.lean', 'AglibTest/AuditSupport.lean', 'AglibTest/AuditCoverage.lean',
    'scripts/check_negative_controls.py', 'scripts/resource_guard.py', 'scripts/build_serial.py',
    'scripts/ci_pipeline.py', 'scripts/ci_state.py', 'scripts/ci_baseline.py',
    'scripts/ci_audit.py',
    'scripts/library_sources.py', 'scripts/check_affected.py', 'scripts/prepare_downstream.py',
    'scripts/run_declaration_linter.py', 'scripts/run_style_linter.py',
    'scripts/check_compiled_inventory.py',
}
TOOL_TESTS = {
    'affected_scope.py': ['test_affected_scope'],
    'check_affected.py': ['test_affected_scope', 'test_ci_pipeline', 'test_ci_state'],
    'check.sh': ['test_check_script', 'test_affected_scope'],
    'build_serial.py': ['test_build_serial', 'test_check_script', 'test_affected_scope'],
    'resource_guard.py': ['test_resource_guard', 'test_build_serial'],
    'cache_ci.py': ['test_cache_ci', 'test_affected_scope'],
    'ci_baseline.py': ['test_ci_baseline', 'test_ci_pipeline', 'test_ci_cache', 'test_affected_scope'],
    'ci_pipeline.py': ['test_ci_pipeline', 'test_ci_integration', 'test_ci_state', 'test_ci_baseline',
                       'test_ci_cache', 'test_affected_scope', 'test_integration_setup', 'test_ci_audit'],
    'ci_audit.py': ['test_ci_audit', 'test_ci_pipeline', 'test_affected_scope', 'test_integration_setup'],
    'ci_state.py': ['test_ci_state', 'test_ci_pipeline', 'test_affected_scope'],
    'check_kernel.py': ['test_kernel'],
    'check_compiled_inventory.py': ['test_integration_setup', 'test_kernel'],
    'run_style_linter.py': ['test_integration_setup', 'test_affected_scope'],
    'run_declaration_linter.py': ['test_affected_scope'],
    'nolints.json': ['test_ci_pipeline', 'test_ci_state'],
    'nolints-style.txt': ['test_ci_pipeline', 'test_integration_setup'],
    'check_negative_controls.py': ['test_integration_setup', 'test_check_script', 'test_affected_scope'],
    'prepare_downstream.py': ['test_integration_setup', 'test_affected_scope'],
    'prepare_build_cache.py': ['test_ci_cache'],
    'cache_key.py': ['test_ci_cache', 'test_kernel'],
    'migration_helpers.py': ['test_migration_helpers'],
    'generate_imports.py': ['test_source_guards'],
    'check_library_layout.py': ['test_source_guards'],
    'check_placeholders.py': ['test_source_guards'],
    'check_source_policy.py': ['test_source_guards'],
    'library_sources.py': ['test_source_guards', 'test_kernel', 'test_integration_setup',
                           'test_ci_cache', 'test_build_serial', 'test_affected_scope'],
}


def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root)


def node(path):
    prefix = 'examples/downstream/'
    return ('client:' + module_name(path[len(prefix):])) if path.startswith(prefix) else module_name(path)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def controls_changed(changed):
    return bool(CONTROL_INPUTS.intersection(changed) or
                any(p.startswith('AglibTest/NegativeControls/') or
                    (p.startswith('ci/') and not p.endswith('.md')) for p in changed))


def cache_imports(graph, targets):
    """Project external imports from the existing local graph, including facades."""
    pending, seen, external = list(targets), set(), set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name in graph:
            pending.extend(graph[name])
        else:
            external.add(name)
    return sorted(external)


def cache_roots(root, plan):
    """Resolve the plan's external imports and pinned linter drivers to Mathlib roots."""
    validate(root, plan)
    if not plan['native']:
        return []
    pending = list(plan['cache_imports'])
    for driver in ('.lake/packages/batteries/scripts/runLinter.lean',
                   '.lake/packages/mathlib/scripts/lint-style.lean'):
        path = root / driver
        if not path.is_file():
            raise ValueError('Missing pinned linter source for cache selection: ' + driver)
        pending.extend(lean_imports(path.read_text()))
    packages = root / '.lake/packages'
    roots, seen = set(), set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name.split('.')[0] in {'Lean', 'Init', 'Std', 'Lake'}:
            continue  # These imports belong to the pinned toolchain.
        if name == 'Mathlib' or name.startswith('Mathlib.'):
            if not (packages / 'mathlib' / module_path(name)).is_file():
                raise ValueError('Missing selected pinned Mathlib source: ' + name)
            roots.add(name)
            continue  # Mathlib's cache follows this module's dependency closure.
        if name.startswith(('Aglib.', 'AglibTest.', 'client:')) or name in {'Aglib', 'AglibTest'}:
            raise ValueError('Missing selected local import source: ' + name)
        matches = [package / module_path(name) for package in packages.iterdir()
                   if package.is_dir() and (package / module_path(name)).is_file()]
        if len(matches) != 1:
            raise ValueError('Missing or ambiguous selected dependency source: ' + name)
        pending.extend(lean_imports(matches[0].read_text()))
    if not roots:
        raise ValueError('No selected Mathlib cache roots; refusing an unscoped cache fetch')
    return sorted(roots)


def select(root, base=None, head=None, full=False, default_base=None, *, allow_configuration_update=False):
    live_head = git(root, 'rev-parse', 'HEAD').decode().strip()
    configuration_update = False
    if full:
        if base or head:
            raise ValueError('--full cannot be combined with --base/--head')
        base_id = None
    else:
        if not base:
            raise ValueError('Incremental checks require --base; use --full only for explicit diagnostics')
        initial = False
        if set(base) == {'0'}:
            parents = git(root, 'rev-list', '--parents', '-n', '1', 'HEAD').decode().split()
            if len(parents) == 1:
                base_id = subprocess.check_output(['git', 'hash-object', '-t', 'tree', '--stdin'],
                                                  cwd=root, input=b'').decode().strip()
                initial = True
            elif default_base:
                base_id = git(root, 'merge-base', 'HEAD', default_base).decode().strip()
            else:
                raise ValueError('New-branch event needs an available --default-base for merge-base selection')
        else:
            base_id = git(root, 'rev-parse', '--verify', base + '^{commit}').decode().strip()
        if head and git(root, 'rev-parse', '--verify', head + '^{commit}').decode().strip() != live_head:
            raise ValueError('--head must identify the checked-out HEAD')
        if head and git(root, 'status', '--porcelain', '--untracked-files=all').strip():
            # Output plans belong outside the checkout when a committed head is selected.
            raise ValueError('--head requires a clean checkout; omit it to include working-tree changes')
    paths = {path.as_posix() for _, path in style_sources(root) if (root / path).is_file()}
    paths |= {p.relative_to(root).as_posix() for p in (root / 'Tools').rglob('*.lean')}
    sources = {node(p): p for p in paths}
    graph = {}
    facades = set()
    for name, path in sources.items():
        text = (root / path).read_text()
        graph[name] = set(lean_imports(text))
        if name.startswith('client:'):
            graph[name] = {('client:' + n) if 'client:' + n in sources else n for n in graph[name]}
        if is_import_surface(text):
            facades.add(name)
    if full:
        changed = sorted(paths)
    else:
        # --no-renames retains both the deleted and new module identities.
        changed = git(root, 'diff', '--name-only', '-z', '--no-renames', base_id,
                      *([head] if head else [])).decode().rstrip('\0').split('\0')
        if not head:
            changed += git(root, 'ls-files', '--others', '--exclude-standard', '-z').decode().rstrip('\0').split('\0')
        changed = sorted(set(filter(None, changed)))
        if (invalid := CONFIG.intersection(changed)) and not initial:
            if not allow_configuration_update:
                raise ValueError('Configuration/pin changes need an explicitly assigned scope: ' + ', '.join(sorted(invalid)))
            configuration_update = True
    reverse = {}
    for name, imports in graph.items():
        for imported in imports:
            reverse.setdefault(imported, set()).add(name)
    # Changed/deleted old imports are necessary for removals and import rewrites.
    if not full:
        for path in changed:
            if not path.endswith('.lean') or path.startswith('ci/'):
                continue
            old = subprocess.run(['git', 'show', base_id + ':' + path], cwd=root, capture_output=True)
            if old.returncode == 0:
                for imported in lean_imports(old.stdout.decode()):
                    if path.startswith('examples/downstream/') and 'client:' + imported in sources:
                        imported = 'client:' + imported
                    reverse.setdefault(imported, set()).add(node(path))
    seeds = set()
    tooling = set()
    for path in changed:
        if path in CONFIG and (full or initial or configuration_update):
            continue
        if path.startswith('ci/') and not path.endswith('.md'):
            tooling.update(['lean-ci', 'test_ci_pipeline', 'test_ci_integration', 'test_ci_state',
                            'test_ci_baseline', 'test_affected_scope', 'test_source_guards',
                            'test_integration_setup', 'test_ci_cache', 'test_ci_audit'])
        elif path.endswith('.lean'):
            if not (path.startswith(('Aglib/', 'AglibTest/', 'Tools/', 'examples/downstream/'))
                    or path in {'Aglib.lean', 'AglibTest.lean'}):
                raise ValueError('Unrecognized Lean source: ' + path)
            seeds.add(node(path))
        elif path.endswith('.md') or (path.startswith('docs/') and path.endswith('.json')):
            continue
        elif path.startswith('scripts/') or path.startswith('.github/'):
            if Path(path).parent == Path('scripts') and path.startswith('scripts/test_') and path.endswith('.py'):
                tooling.add(Path(path).stem)
            elif path.startswith('.github/actions/lake-cache/'):
                tooling.add('native-cache')
                tooling.add('test_ci_cache')
            elif path.startswith('.github/workflows/'):
                tooling.update(['test_ci_baseline', 'test_ci_pipeline', 'test_ci_integration', 'test_ci_state',
                                'test_ci_cache', 'test_affected_scope', 'test_integration_setup', 'native-cache'])
            elif Path(path).parent == Path('scripts') and Path(path).name in TOOL_TESTS:
                tooling.update(TOOL_TESTS[Path(path).name])
            else:
                raise ValueError('Unrecognized tooling path; assign its regression scope explicitly: ' + path)
        elif path.endswith(('.md', '.json')) or path in {'LICENSE', '.gitignore', '.gitattributes'}:
            continue
        else:
            raise ValueError('Unrecognized changed path; assign its validation explicitly: ' + path)
    affected, pending = set(seeds), list(seeds)
    while pending:
        for consumer in reverse.get(pending.pop(), set()) - affected:
            affected.add(consumer)
            pending.append(consumer)
    if configuration_update:
        # A dependency/compiler/configuration transition assigns complete current
        # check coverage. Lake still decides which compiler outputs need work.
        seeds.update(sources)
        affected.update(sources)
        tooling.update(['test_ci_pipeline', 'test_ci_cache', 'test_cache_ci', 'test_integration_setup'])
    executable = affected & sources.keys()
    # The legacy whole-library audit is replaced by a selected-origin audit.
    executable -= {'AglibTest.Axioms', 'client:Audit'}
    executable = {n for n in executable if 'NegativeControls' not in n.split('.')}
    providers = sorted(n for n in (executable & seeds) - facades if n.startswith('Aglib.') or n.startswith('Tools.'))
    consumers = sorted(n for n in executable - set(providers) if n == 'Aglib' or n.startswith(('Aglib.', 'Tools.')))
    tests = sorted(n for n in executable if (n == 'AglibTest' or n.startswith('AglibTest.')) and n != 'AglibTest.AuditSupport')
    client = sorted(n.removeprefix('client:') for n in executable if n.startswith('client:'))
    controls = bool(full or controls_changed(changed))
    trust = bool((executable - {n for n in executable if n.startswith('client:')})
                 or seeds & AUDIT or controls)
    client_audit = bool(client or 'client:Audit' in seeds)
    native = bool(providers or consumers or tests or client_audit or trust)
    cache_targets = providers + consumers + tests + ['client:' + name for name in client]
    if trust:
        cache_targets += [name for name in graph if name in {'AglibTest.AuditSupport', 'AglibTest.AuditCoverage'}]
        if controls:
            cache_targets += [name for name in graph if name.startswith('AglibTest.NegativeControls.')]
        if 'AglibTest/Axioms.lean' in changed:
            cache_targets.append('AglibTest.Axioms')
    if client_audit:
        cache_targets.append('client:Audit')
    identity_paths = set(changed) | {sources[n] for n in affected if n in sources} | CONFIG
    if trust:
        identity_paths.update(['AglibTest/Axioms.lean', 'AglibTest/AuditSupport.lean',
                               'AglibTest/AuditCoverage.lean'])
    return {'schema': 1, 'coverage': 'explicit-full' if full else 'affected-only',
            'base': base_id, 'head': live_head, 'working_tree': not bool(head), 'changed': changed,
            'configuration_update': configuration_update,
            'providers': providers, 'consumers': consumers, 'tests': tests, 'client': client,
            'cache_imports': cache_imports(graph, cache_targets) if native else [],
            'facades': sorted(facades & affected),
            'imports': {n: sorted(graph[n]) for n in facades & affected},
            'style': sorted(n for n in affected & sources.keys() if (configuration_update or sources[n] in changed) and not n.startswith('client:')
                            and 'NegativeControls' not in n),
            'trust': trust, 'controls': controls, 'client_audit': client_audit, 'native': native,
            'publish': bool(providers or consumers or tests or trust), 'tooling_tests': sorted(tooling),
            'identity': {p: digest(root / p) for p in sorted(identity_paths)}}


def validate(root, plan):
    if plan['head'] != git(root, 'rev-parse', 'HEAD').decode().strip():
        raise ValueError('Plan HEAD changed; select the current affected scope again')
    for path, expected in plan['identity'].items():
        if digest(root / path) != expected:
            raise ValueError('Plan input changed: ' + path)
    if plan['coverage'] == 'affected-only':
        if not plan['working_tree']:
            if git(root, 'status', '--porcelain', '--untracked-files=all').strip():
                raise ValueError('Committed plan acquired working-tree changes')
        else:
            changed = git(root, 'diff', '--name-only', '-z', '--no-renames', plan['base']).decode().split('\0')
            changed += git(root, 'ls-files', '--others', '--exclude-standard', '-z').decode().split('\0')
            if set(filter(None, changed)) != set(plan['changed']):
                raise ValueError('Changed-path scope drifted; select the current affected scope again')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--base')
    parser.add_argument('--head')
    parser.add_argument('--default-base', help='trusted default-branch ref, used only for an all-zero new-branch event base')
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--github-output', type=Path)
    parser.add_argument('--cache-roots', type=Path, metavar='PLAN',
                        help='project validated selected cache roots after pinned dependencies are resolved')
    args = parser.parse_args()
    try:
        if args.cache_roots:
            if args.base or args.head or args.full or args.output or args.github_output or args.default_base:
                raise ValueError('--cache-roots consumes a plan instead of selection arguments')
            roots = cache_roots(args.root.resolve(), json.loads(args.cache_roots.read_text()))
            if roots:
                print('\n'.join(roots))
            return 0
        plan = select(args.root.resolve(), args.base, args.head, args.full, args.default_base)
        text = json.dumps(plan, indent=2) + '\n'
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(text)
            print(f"Affected scope: base={plan['base']} head={plan['head']} "
                  f"providers={len(plan['providers'])} consumers={len(plan['consumers'])} "
                  f"tests={len(plan['tests'])} client={len(plan['client'])} "
                  f"native={str(plan['native']).lower()}")
        else:
            print(text, end='')
        if args.github_output:
            with args.github_output.open('a') as output:
                output.write('native=' + str(plan['native']).lower() + '\n')
                output.write('publish=' + str(plan['publish']).lower() + '\n')
        return 0
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print('Scope selection failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
