#!/usr/bin/env python3
"""Check production/test enrollment, import boundaries, resolution and cycles."""
import argparse
from pathlib import Path
import sys

from .generate_imports import generator_owned, stale_files
from .library_sources import (downstream_sources, lean_imports, module_name,
                             module_path, source_modules, test_modules,
                             is_import_surface)

ROOT = Path.cwd()
FORBIDDEN = {'audit', 'audits', 'consumer', 'test', 'tests', 'quillentest'}
FORBIDDEN_ROOTS = {'tools', 'scripts'}


def import_cycles(graph: dict[str, set[str]]) -> list[str]:
    """Iterative DFS avoids Python recursion limits for long source chains."""
    state = {}
    cycles = []
    for entry in sorted(graph):
        if state.get(entry):
            continue
        state[entry] = 1
        stack = [(entry, iter(sorted(graph[entry])))]
        while stack:
            module, children = stack[-1]
            child = next(children, None)
            if child is None:
                state[module] = 2
                stack.pop()
            elif state.get(child) == 1:
                cycles.append(f'{module} -> {child}')
            elif child in graph and not state.get(child):
                state[child] = 1
                stack.append((child, iter(sorted(graph[child]))))
    return cycles


def check_layout(root: Path) -> tuple[list[str], int]:
    errors = []
    modules, tests = source_modules(root), test_modules(root)
    loose = {path.name for path in root.glob('*.lean')} - {'Quillen.lean', 'QuillenTest.lean'}
    if loose:
        errors.append(f'Unclassified project-root Lean files: {sorted(loose)}')
    stale = stale_files(root)
    if stale:
        errors.append(f'Stale generated imports (missing enrollment or changed facade): {stale}; '
                      'run lean-tools quillen imports')
    graph = {}
    clients = downstream_sources(root)
    client_root = root / 'examples/downstream'
    client_roots = {path.stem for path in client_root.glob('*.lean')} | {
        path.parts[2] for path in clients if len(path.parts) > 3}
    paths = modules | tests | clients
    topic_facades = {path for path in modules if path != Path('Quillen.lean')
                     and (root / path.with_suffix('')).is_dir()
                     and (generator_owned((root / path).read_text())
                          or is_import_surface((root / path).read_text()))}
    for facade in sorted(modules - {Path('Quillen.lean')}):
        path = root / facade
        if path.exists() and generator_owned(path.read_text()) and not path.with_suffix('').is_dir():
            errors.append(f'Generator-owned facade has no corresponding directory: {facade}')
    for relative in sorted(paths):
        path = root / relative
        if not path.is_file():
            errors.append(f'Missing project import source: {relative}')
            continue
        imports = set(lean_imports(path.read_text()))
        library = relative in modules
        for imported in sorted(imports):
            parts = imported.split('.')
            forbidden = (parts[0].strip('«»').casefold() in FORBIDDEN_ROOTS
                         or any(part.strip('«»').casefold() in FORBIDDEN for part in parts))
            if library and forbidden:
                errors.append(f'Forbidden library import in {relative}: {imported}')
            # Production and trust-test modules resolve in the root package;
            # independently configured Consumer modules resolve in their package.
            target = None
            if parts[0] in {'Quillen', 'QuillenTest'}:
                target = root / module_path(imported)
            elif relative in clients and parts[0] in client_roots:
                target = client_root / module_path(imported)
            if target is not None and not target.is_file():
                errors.append(f'Unresolved local import in {relative}: {imported}')
            if library and len(relative.parts) > 2 and relative not in topic_facades and (
                    imported == 'Quillen' or (parts[0] == 'Quillen' and len(parts) == 2)
                    or module_path(imported) in topic_facades):
                errors.append(f'Implementation imports broad facade in {relative}: {imported}')
        if relative in modules | tests:
            graph[module_name(relative)] = {name for name in imports
                if name.split('.')[0] in {'Quillen', 'QuillenTest'}}
    errors.extend('Project import cycle: ' + cycle for cycle in import_cycles(graph))
    return errors, len(modules)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args(argv)
    try:
        errors, count = check_layout(args.root)
    except (OSError, ValueError, KeyError) as error:
        print(f'Layout check failed: {error}', file=sys.stderr)
        return 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'Library layout checked: {count} production modules; '
          f'{len(test_modules(args.root))} test modules; thematic facade enrollment; '
          'no forbidden or unresolved local imports or cycles.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
