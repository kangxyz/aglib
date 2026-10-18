#!/usr/bin/env python3
"""Check occupied-source enrollment, modern exports, import resolution and cycles.

This is an exact source-graph guard, not acceptance of mathematical premises.
"""
import argparse
from pathlib import Path
import re
import sys

from generate_imports import generator_owned, stale_files
from library_sources import (audit_sources, downstream_sources, is_import_surface,
                             lean_imports, module_name, module_path, source_modules,
                             strip_comments_and_strings, test_modules, uses_module_system)

ROOT = Path(__file__).resolve().parents[1]
PROJECT = 'Aglib'
TEST = 'AglibTest'
# These are module identities, never declaration namespace restrictions.
OLD_ROOTS = {'r5lab', 'quillen', 'essays', 'tests', 'oldtests', 'quillentest',
             'r5labtest', 'tools', 'scripts', 'audit', 'audits'}
APPLICATION_COMPONENTS = {'curve', 'curves', 'genus', 'p1', 'projectiveline', 'degree',
    'riemannroch', 'rr', 'ktheory', 'gtheory', 'qconstruction', 'sconstruction',
    'plus', 'plusconstruction', 'bass', 'spectra', 'prespectrum', 'prespectra',
    'perfectcomplex', 'k', 'g', 'q', 's'}

# One-file exception to the public-import rule. Mathlib does not expose the body of
# `Module.Grassmannian.baseChangeMkQ`; this leaf alone reads it to supply the
# `BaseChangeMkQFormula` instance. Remove the entry and the file once Mathlib exposes
# `baseChangeMkQ` or publishes `baseChangeMkQ_tmul`.
PRIVATE_IMPORT_EXCEPTIONS = {
    Path('Aglib/RingTheory/Grassmannian/BaseChangeFormula.lean'):
        'import all Mathlib.RingTheory.Grassmannian',
}


def forbidden_domain_import(name: str) -> bool:
    raw_parts = [part.strip('«»') for part in name.split('.')]
    if raw_parts[0] in {'AGLib', 'AGLibTest'}:
        return True
    parts = [part.casefold() for part in raw_parts]
    if parts[0] in OLD_ROOTS:
        return True
    if parts[0] != PROJECT.casefold():
        return False
    for index, part in enumerate(parts[1:], 1):
        # These owners use Plus for actual bounded-below complexes/categories,
        # unrelated to a plus-construction application family.
        bounded_below = part == 'plus' and parts[:index] in [
            [PROJECT.casefold(), 'algebra', 'homology', 'derivedcategory'],
            [PROJECT.casefold(), 'algebra', 'homology', 'homotopycategory'],
            [PROJECT.casefold(), 'algebraicgeometry', 'cohomology', 'cech', 'resolution']]
        # These two leaves transport homology/exterior degrees in regular-list
        # purity; they do not belong to the downstream degree application family.
        canonical_degree = part == 'degree' and index == len(parts) - 1 and parts[:index] in [
            [PROJECT.casefold(), 'algebraicgeometry', 'cohomology', 'duality',
             'projective', 'canonical', 'localmodel', 'class'],
            [PROJECT.casefold(), 'algebraicgeometry', 'cohomology', 'duality',
             'projective', 'canonical', 'localmodel', 'insertion']]
        if part in APPLICATION_COMPONENTS and not (bounded_below or canonical_degree):
            return True
    return False


def import_cycles(graph: dict[str, set[str]]) -> list[str]:
    """Iterative DFS also handles source chains longer than Python recursion limits."""
    state, cycles = {}, []
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
    modules, tests, audits = source_modules(root), test_modules(root), audit_sources(root)
    loose = {path.name for path in root.glob('*.lean')} - {PROJECT + '.lean', TEST + '.lean'}
    if loose:
        errors.append(f'Unclassified project-root Lean files: {sorted(loose)}')
    try:
        stale = stale_files(root)
        if stale:
            errors.append(f'Stale generated imports (missing enrollment or changed facade): {stale}; '
                          'run python3 scripts/generate_imports.py')
    except ValueError as error:
        errors.append(str(error))
    graph = {}
    clients = downstream_sources(root)
    client_root = root / 'examples/downstream'
    client_roots = {path.stem for path in client_root.glob('*.lean')} | {
        path.parts[2] for path in clients if len(path.parts) > 3}
    topic_facades = {path for path in modules if path != Path(PROJECT + '.lean')
                     and (root / path.with_suffix('')).is_dir()
                     and (generator_owned((root / path).read_text())
                          or is_import_surface((root / path).read_text()))}
    for facade in sorted(modules - {Path(PROJECT + '.lean')}):
        path = root / facade
        if path.exists() and generator_owned(path.read_text()) and not path.with_suffix('').is_dir():
            errors.append(f'Generator-owned facade has no corresponding directory: {facade}')
    for auditor in (Path(TEST + '/Axioms.lean'), Path(TEST + '/AuditSupport.lean'),
                    Path('examples/downstream/Audit.lean')):
        path = root / auditor
        if path.exists() and uses_module_system(path.read_text()):
            errors.append(f'Exhaustive axiom auditor must retain legacy private imports: {auditor}')
    for relative in sorted(modules | tests | audits | clients):
        path = root / relative
        if not path.is_file():
            errors.append(f'Missing project import source: {relative}')
            continue
        source = path.read_text()
        clean = strip_comments_and_strings(source)
        imports = set(lean_imports(source))
        library = relative in modules
        if library:
            if not uses_module_system(source):
                errors.append(f'Production source lacks modern module header: {relative}')
            if not is_import_surface(source) and not re.search(
                    r'@\[\s*expose\s*\]\s*public\s+section\b', clean):
                errors.append(f'Production implementation lacks exposed public section: {relative}')
            for match in re.finditer(r'^[ \t]*(?:(?:private|meta)[ \t]+)*import\b', clean, re.M):
                line = clean[match.start():clean.find('\n', match.start())].strip()
                if PRIVATE_IMPORT_EXCEPTIONS.get(relative) == line:
                    continue
                errors.append(f'Production import lacks public modifier: {relative}: '
                              f'line {source.count(chr(10), 0, match.start()) + 1}')
        for imported in sorted(imports):
            parts = imported.split('.')
            if forbidden_domain_import(imported):
                errors.append(f'Forbidden domain import in {relative}: {imported}')
            if library and parts[0] not in {PROJECT, 'Mathlib'}:
                errors.append(f'Forbidden library import in {relative}: {imported}')
            target = None
            if parts[0] in {PROJECT, TEST}:
                target = root / module_path(imported)
            elif relative in clients and parts[0] in client_roots:
                target = client_root / module_path(imported)
            if target is not None and not target.is_file():
                errors.append(f'Unresolved local import in {relative}: {imported}')
            if library and relative not in topic_facades | {Path(PROJECT + '.lean')} and (
                    imported == PROJECT or module_path(imported) in topic_facades):
                errors.append(f'Implementation imports broad facade in {relative}: {imported}')
            if relative in tests and module_path(imported) in audits:
                errors.append(f'Positive fixture imports audit or negative control: {relative}: {imported}')
        if relative in modules | tests | audits:
            graph[module_name(relative)] = {name for name in imports
                if name.split('.')[0] in {PROJECT, TEST}}
    errors.extend('Project import cycle: ' + cycle for cycle in import_cycles(graph))
    return errors, len(modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    try:
        errors, count = check_layout(args.root)
    except (OSError, ValueError, KeyError) as error:
        print(f'Layout check failed: {error}', file=sys.stderr)
        return 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'Library layout checked: {count} production modules; '
          f'{len(test_modules(args.root))} positive modules; no forbidden imports or cycles.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
