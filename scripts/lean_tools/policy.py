"""One source-policy engine, configured by the selected library's existing rules."""
import argparse
import json
from pathlib import Path
import re
import sys

from .library import configuration, profile
from .source import (client_sources, import_cycles, is_import_surface, lean_imports,
                     source_modules, strip_comments_and_strings)


def forbidden_import(name, data):
    parts = [part.strip('«»') for part in name.split('.')]
    folded = [part.casefold() for part in parts]
    return (parts[0] in data.get('forbidden_roots_exact', ())
            or folded[0] in data.get('forbidden_roots_folded', ())
            or any(part in data.get('forbidden_components', ()) for part in folded))


def check_configuration(root):
    root = Path(root)
    data = profile(root)
    pins = data.get('accepted_pins')
    if not pins:
        return []
    errors = []
    production, test = data['production'], data['production'] + 'Test'
    try:
        config = configuration(root)
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        if config.get('name') != data['package'] or manifest.get('name') != data['package']:
            errors.append(f'Package and manifest names must both be {data["package"]}')
        libraries = {entry.get('name') for entry in config.get('lean_lib', [])}
        if libraries != {production, test}:
            errors.append(f'Lean libraries must be exactly {production} and {test}')
        if config.get('testDriver') != test:
            errors.append(f'testDriver must be {test}')
        defaults = config.get('defaultTargets', [])
        if production not in defaults or not set(defaults) <= libraries:
            errors.append(f'defaultTargets must include {production} and use only declared libraries')
        requires = {entry['name']: entry for entry in config.get('require', [])}
        packages = {entry['name']: entry for entry in manifest.get('packages', [])}
        if len(packages) != len(manifest.get('packages', [])):
            errors.append('Duplicate dependency names in manifest')
        if set(requires) != set(pins):
            errors.append('Direct dependencies must be exactly ' + ', '.join(pins))
        for name, (url, revision) in pins.items():
            requirement, package = requires.get(name, {}), packages.get(name, {})
            if requirement.get('git') != url or requirement.get('rev') != revision:
                errors.append(f'{name}: lakefile must retain the accepted Git URL and exact pin')
            if (package.get('url') != url or package.get('rev') != revision
                    or package.get('inputRev') != revision or package.get('type') != 'git'
                    or package.get('inherited') is not False):
                errors.append(f'{name}: manifest differs from the accepted direct dependency')
        for package in packages.values():
            if package.get('type') != 'git' or not re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')):
                errors.append(f'{package.get("name")}: manifest dependency lacks an exact Git SHA')
        if (root / 'lean-toolchain').read_text().strip() != data['toolchain']:
            errors.append('lean-toolchain must retain ' + data['toolchain'])
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append(f'Package configuration: {error}')
    return errors


def check_sources(root, checks=('layout', 'tokens', 'policy'), *, generated=False):
    from .imports import generator_owned, check_generated
    root, checks = Path(root), set(checks)
    data = profile(root)
    if 'source_tokens' not in data:
        raise ValueError(f'{data["package"]} uses native CI checks. Run lean-tools check.')
    production, test = data['production'], data['production'] + 'Test'
    sources, clients = source_modules(root), client_sources(root)
    texts = {name: path.read_text() for name, path in sources.items()}
    client_texts = {name: path.read_text() for name, path in clients.items()}
    errors, graph = [], {}
    if 'layout' in checks and production not in sources:
        errors.append(f'Missing public source root: {production}.lean')
    if 'layout' in checks and data.get('classify_root'):
        loose = {path.name for path in root.glob('*.lean')} - {production + '.lean', test + '.lean'}
        if loose:
            errors.append(f'Unclassified project-root Lean files: {sorted(loose)}')
    facades = {name for name, path in sources.items() if name != production
               and name.startswith(production + '.') and path.with_suffix('').is_dir()
               and (is_import_surface(texts[name]) or generator_owned(texts[name], data))}
    client_roots = {name.split('.')[0] for name in clients}
    forbidden_tokens = re.compile(data.get('source_token_pattern', r'\b({tokens})\b').format(
        tokens='|'.join(data['source_tokens'])))
    records = [(False, name, path, texts[name]) for name, path in sources.items()]
    records += [(True, name, path, client_texts[name]) for name, path in clients.items()]
    for client, name, path, source in sorted(records):
        relative = path.relative_to(root)
        clean = strip_comments_and_strings(source)
        library = not client and (name == production or name.startswith(production + '.'))
        imports = set(lean_imports(source))
        if 'tokens' in checks:
            for match in forbidden_tokens.finditer(clean):
                line = source.count('\n', 0, match.start()) + 1
                errors.append(f'{relative}:{line}: forbidden token {match[0]}')
        if 'policy' in checks:
            if data.get('reject_root_namespace'):
                for match in re.finditer(r'^[ \t]*namespace\s+_root_(?=\.|\s|$)', clean, re.M):
                    line = source.count('\n', 0, match.start()) + 1
                    errors.append(f'{relative}:{line}: namespace _root_ does not escape '
                                  'enclosing namespaces; close and reopen namespaces instead')
            if library:
                pattern = data.get('production_components')
                if pattern:
                    invalid = [part for part in name.split('.') if not re.fullmatch(pattern, part)]
                    if invalid:
                        errors.append(f'{name}: production module components must use PascalCase '
                                      '([A-Z][A-Za-z0-9_]*): ' + ', '.join(invalid))
        if 'layout' not in checks:
            continue
        key = ('client:' if client else '') + name
        if not client or data.get('strict_client'):
            graph[key] = {('client:' if client else '') + item
                          for item in imports & (clients.keys() if client else sources.keys())}
        for imported in sorted(imports):
            prefix = imported.split('.')[0]
            if (library or data.get('forbidden_scope') == 'all') and forbidden_import(imported, data):
                errors.append(f'Forbidden library import in {relative}: {imported}')
                continue
            if client:
                if prefix in {production, test}:
                    if prefix == test and data.get('strict_client'):
                        errors.append(f'client {name}: forbidden test/obsolete import {imported}')
                    elif imported not in sources:
                        errors.append(f'Unresolved local import (missing project import) in client {name}: {imported}')
                elif prefix in client_roots and imported not in clients:
                    errors.append(f'Unresolved local import (missing client import) in client {name}: {imported}')
                elif data.get('strict_client') and prefix not in client_roots and prefix not in data.get('external_roots', ()):
                    errors.append(f'client {name}: unknown external import root {imported}')
                continue
            if data.get('strict_client') and prefix in client_roots:
                errors.append(f'{name}: project source imports independent client {imported}')
            elif prefix in {production, test}:
                if imported not in sources:
                    errors.append(f'Unresolved local import in {name}: missing local import {imported}')
                if library and prefix == test:
                    errors.append(f'Forbidden library import in {name}: production imports test {imported}')
                candidate = data.get('candidate')
                if candidate and (name == candidate or name.startswith(candidate + '.')) and prefix == production and not (
                        imported == candidate or imported.startswith(candidate + '.')):
                    errors.append(f'{name}: candidate imports host module {imported}; local dependencies must stay within {candidate}')
            elif data.get('external_roots') and prefix not in data['external_roots']:
                errors.append(f'{name}: unknown external import root {imported}')
            mode = data.get('broad_facades')
            implementation = library and name != production and name not in facades
            if mode == 'top-level':
                implementation = implementation and len(relative.parts) > 2
            broad = imported == production or imported in facades or (
                mode == 'top-level' and prefix == production and len(imported.split('.')) == 2)
            if mode and implementation and broad:
                errors.append(f'Implementation imports broad facade in {relative}: {imported}')
    if 'layout' in checks:
        errors.extend('Project import cycle: ' + route for route in import_cycles(graph))
        if generated:
            errors.extend(f'Generator-owned facade has no corresponding directory: {path.relative_to(root)}'
                for name, path in sources.items() if name not in {production, test}
                and generator_owned(texts[name], data) and not path.with_suffix('').is_dir())
            errors.extend(check_generated(root, sources=sources, texts=texts))
    return errors, len(sources) + len(clients)


def check_repository(root):
    errors, count = check_sources(root, generated=True)
    return check_configuration(root) + errors, count


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--only', choices=('layout', 'tokens', 'policy'))
    args = parser.parse_args(argv)
    try:
        errors, count = (check_sources(args.root, (args.only,), generated=args.only == 'layout')
                         if args.only else check_repository(args.root))
    except (OSError, ValueError, KeyError) as error:
        print('Source inspection failed: ' + str(error), file=sys.stderr)
        return 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'Checked {count} Lean sources using the shared source-policy engine.')
    return 0
