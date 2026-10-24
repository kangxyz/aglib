#!/usr/bin/env python3
# Authors: kangxyz
"""Check source boundaries and fixed dependency identities, without invoking Lake."""
import argparse
import json
from pathlib import Path
import re
import sys
import tomllib

from .imports import check_generated
from .sources import client_sources, lean_imports, source_modules, strip_comments_and_strings

ROOT = Path.cwd()
PINS = {
    'mathlib': ('https://github.com/leanprover-community/mathlib4.git',
                'd13f23b723b8a846827a245b89c10fc7d3f11612'),
    'Aglib': ('https://github.com/kangxyz/aglib.git',
              '2c34f185fa859e862661f939cd216b07bcccfb26'),
}
EXTERNAL_ROOTS = {'Mathlib', 'Aglib', 'Lean', 'Init', 'Std', 'Batteries',
                  'Aesop', 'Qq', 'ProofWidgets', 'ImportGraph', 'Plausible',
                  'LeanSearchClient', 'Cli'}
OBSOLETE_ROOTS = {'Tests', 'R5Lab', 'R5LabTest', 'Quillen', 'QuillenTest'}
PRODUCTION_COMPONENT = re.compile(r'[A-Z][A-Za-z0-9_]*')
ROOT_NAMESPACE = re.compile(r'^[ \t]*namespace\s+_root_(?=\.|\s|$)', re.M)
FORBIDDEN = re.compile(r'(?<![\w\'])\b(sorry|admit|axiom|unsafe|native_decide)\b(?![\w\'])')


def check_configuration(root: Path) -> list[str]:
    errors = []
    try:
        config = tomllib.loads((root / 'lakefile.toml').read_text())
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        if config.get('name') != 'Motivic' or manifest.get('name') != 'Motivic':
            errors.append('Package and manifest names must both be Motivic')
        libraries = {entry.get('name') for entry in config.get('lean_lib', [])}
        if libraries != {'Motivic', 'MotivicTest'}:
            errors.append('Lean libraries must be exactly Motivic and MotivicTest')
        if config.get('testDriver') != 'MotivicTest':
            errors.append('testDriver must be MotivicTest')
        defaults = config.get('defaultTargets', [])
        if 'Motivic' not in defaults or not set(defaults) <= libraries:
            errors.append('defaultTargets must include Motivic and use only declared libraries')
        requires = {entry['name']: entry for entry in config.get('require', [])}
        packages = {entry['name']: entry for entry in manifest.get('packages', [])}
        if len(packages) != len(manifest.get('packages', [])):
            errors.append('Duplicate dependency names in manifest')
        if set(requires) != set(PINS):
            errors.append('Direct dependencies must be exactly mathlib and Aglib')
        for name, (url, revision) in PINS.items():
            requirement, package = requires.get(name, {}), packages.get(name, {})
            if requirement.get('git') != url or requirement.get('rev') != revision:
                errors.append(f'{name}: lakefile must retain the accepted Git URL and exact pin')
            if (package.get('url') != url or package.get('rev') != revision
                    or package.get('inputRev') != revision or package.get('type') != 'git'
                    or package.get('inherited') is not False):
                errors.append(f'{name}: manifest differs from the accepted direct dependency')
        for package in packages.values():
            if package.get('type') != 'git' or not re.fullmatch(
                    r'[0-9a-f]{40}', package.get('rev', '')):
                errors.append(f'{package.get("name")}: manifest dependency lacks an exact Git SHA')
        if (root / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.1':
            errors.append('lean-toolchain must retain leanprover/lean4:v4.34.1')
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append(f'Package configuration: {error}')
    return errors


def import_cycles(graph: dict[str, set[str]]) -> list[str]:
    """Use iterative DFS so long mathematical dependency chains remain supported."""
    state, errors = {}, []
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
                route = [item[0] for item in stack]
                start = route.index(child)
                errors.append('Import cycle: ' + ' -> '.join(route[start:] + [child]))
            elif child in graph and not state.get(child):
                state[child] = 1
                stack.append((child, iter(sorted(graph[child]))))
    return errors


def check_sources(root: Path) -> tuple[list[str], int]:
    errors, graph = [], {}
    sources = source_modules(root)
    clients = client_sources(root)
    client_roots = {name.split('.')[0] for name in clients}
    if 'Motivic' not in sources:
        errors.append('Missing public source root: Motivic.lean')
    for name, path in sorted(sources.items()):
        source = path.read_text()
        clean = strip_comments_and_strings(source)
        for match in FORBIDDEN.finditer(clean):
            line = clean.count('\n', 0, match.start()) + 1
            errors.append(f'{path.relative_to(root)}:{line}: forbidden token {match[0]}')
        for match in ROOT_NAMESPACE.finditer(clean):
            line = clean.count('\n', 0, match.start()) + 1
            errors.append(f'{path.relative_to(root)}:{line}: namespace _root_ does not escape '
                          'enclosing namespaces; close and reopen namespaces instead')
        imports = set(lean_imports(source))
        graph[name] = imports & sources.keys()
        production = name == 'Motivic' or name.startswith('Motivic.')
        candidate = name == 'Motivic.Aglib' or name.startswith('Motivic.Aglib.')
        if production:
            invalid = [part for part in name.split('.') if not PRODUCTION_COMPONENT.fullmatch(part)]
            if invalid:
                errors.append(f'{name}: production module components must use PascalCase '
                              '([A-Z][A-Za-z0-9_]*): ' + ', '.join(invalid))
        for imported in sorted(imports):
            prefix = imported.split('.')[0]
            if prefix in client_roots:
                errors.append(f'{name}: project source imports independent client {imported}')
            elif prefix in OBSOLETE_ROOTS:
                errors.append(f'{name}: obsolete import {imported}')
            elif prefix in {'Motivic', 'MotivicTest'}:
                if imported not in sources:
                    errors.append(f'{name}: missing local import {imported}')
                if production and prefix == 'MotivicTest':
                    errors.append(f'{name}: production imports test {imported}')
                if candidate and prefix == 'Motivic' and not (
                        imported == 'Motivic.Aglib' or imported.startswith('Motivic.Aglib.')):
                    errors.append(f'{name}: candidate imports host module {imported}; '
                                  'local dependencies must stay within Motivic.Aglib')
            elif prefix not in EXTERNAL_ROOTS:
                errors.append(f'{name}: unknown external import root {imported}')
    errors.extend(import_cycles(graph))
    client_graph = {}
    for name, path in sorted(clients.items()):
        source = path.read_text()
        clean = strip_comments_and_strings(source)
        for match in FORBIDDEN.finditer(clean):
            line = clean.count('\n', 0, match.start()) + 1
            errors.append(f'{path.relative_to(root)}:{line}: forbidden token {match[0]}')
        for match in ROOT_NAMESPACE.finditer(clean):
            line = clean.count('\n', 0, match.start()) + 1
            errors.append(f'{path.relative_to(root)}:{line}: namespace _root_ does not escape '
                          'enclosing namespaces; close and reopen namespaces instead')
        imports = set(lean_imports(source))
        client_graph['client:' + name] = {'client:' + item for item in imports & clients.keys()}
        for imported in sorted(imports):
            prefix = imported.split('.')[0]
            if prefix == 'Motivic':
                if imported not in sources:
                    errors.append(f'client {name}: missing project import {imported}')
            elif prefix == 'MotivicTest' or prefix in OBSOLETE_ROOTS:
                errors.append(f'client {name}: forbidden test/obsolete import {imported}')
            elif prefix in client_roots:
                if imported not in clients:
                    errors.append(f'client {name}: missing client import {imported}')
            elif prefix not in EXTERNAL_ROOTS:
                errors.append(f'client {name}: unknown external import root {imported}')
    errors.extend(import_cycles(client_graph))
    return errors, len(sources) + len(clients)


def check_repository(root: Path) -> tuple[list[str], int]:
    errors, count = check_sources(root)
    return check_configuration(root) + errors + check_generated(root), count


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args(argv)
    try:
        errors, count = check_repository(args.root.resolve())
    except (OSError, UnicodeError) as error:
        print(f'Source inspection failed: {error}', file=sys.stderr)
        return 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    client_count = len(client_sources(args.root.resolve()))
    print(f'Checked {count} Lean sources ({count - client_count} project, {client_count} downstream): '
          'local imports, DAG, generated facades, isolation, source tokens and pins.')
    print('External import paths require dependency resolution and Lean compilation; source checks do not prove them.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
