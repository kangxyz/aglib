"""Scoped native cache recovery shared by every supported Lean library."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import subprocess
import sys

from .library import family, local_roots
from .source import lean_imports, module_path, MODULE


def workspace_imports(root, targets=None):
    root = Path(root)
    roots = local_roots(root)
    if not roots:
        raise ValueError('No local Lean library roots are configured')
    if targets:
        pending = []
        for name in targets:
            path = module_path(name)
            if name.split('.')[0] not in roots or not (root / path).is_file():
                raise ValueError('Expected existing local cache target: ' + name)
            pending.append(path)
    else:
        pending = [path.relative_to(root) for name in roots
                   for path in (root / name).rglob('*.lean')]
        pending += [Path(name + '.lean') for name in roots if (root / (name + '.lean')).is_file()]
        pending += [path.relative_to(root) for path in (root / 'examples/downstream').rglob('*.lean')
                    if '.lake' not in path.relative_to(root).parts]
    seen, imports = set(), set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for name in lean_imports((root / path).read_text()):
            imports.add(name)
            if name.split('.')[0] in roots:
                local = module_path(name)
                if not (root / local).is_file():
                    raise ValueError('Missing reachable local source: ' + str(root / local))
                pending.append(local)
    return imports


def mathlib_cache_roots(root, imports=None):
    """Follow reachable pinned Aglib sources, never enumerate unrelated modules."""
    root = Path(root)
    pending = list(workspace_imports(root) if imports is None else imports)
    local = local_roots(root)
    seen, modules = set(), set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        prefix = name.split('.')[0]
        if prefix == 'Mathlib':
            if name == 'Mathlib':
                raise ValueError('Whole Mathlib imports are not a focused cache input')
            modules.add(name)
        elif prefix == 'Aglib' and prefix not in local:
            path = root / '.lake/packages/Aglib' / module_path(name)
            if not path.is_file():
                raise ValueError('Missing reachable pinned Aglib source: ' + str(path))
            pending.extend(lean_imports(path.read_text()))
    if not modules:
        raise ValueError('No reachable Mathlib imports; refusing an unscoped cache download')
    return sorted(modules)


def cache_roots(root, targets=None):
    return mathlib_cache_roots(root, workspace_imports(root, targets))


def validate_command(command, root):
    if command[:4] != ['lake', 'exe', 'cache', 'get'] or len(command) == 4:
        raise ValueError('Cache bootstrap requires explicit Mathlib/Batteries leaf roots')
    for name in command[4:]:
        if MODULE.fullmatch(name) is None or not name.startswith(('Mathlib.', 'Batteries.')):
            raise ValueError('Cache bootstrap requires explicit Mathlib/Batteries leaf roots')
        dependency = 'mathlib' if name.startswith('Mathlib.') else 'batteries'
        path = Path(root) / '.lake/packages' / dependency / module_path(name)
        if not path.is_file():
            raise ValueError('Missing focused cache source: ' + name)


def run(root, command, receipt):
    validate_command(command, root)
    from .cli import main
    return main(['run', '--root', str(root), '--receipt', str(receipt), '--bootstrap-cache', '--', *command])


def bootstrap_main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    try:
        return run(args.root.resolve(), command, args.receipt)
    except (OSError, ValueError, ImportError, subprocess.SubprocessError) as error:
        print('Focused cache bootstrap failed: ' + str(error), file=sys.stderr)
        return 125


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--resolve-deps', action='store_true')
    parser.add_argument('--lint-runtime', action='store_true')
    parser.add_argument('--guarded', '--ci', action='store_true')
    parser.add_argument('targets', nargs='*')
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        imports = workspace_imports(root, args.targets)
        if args.list and args.resolve_deps:
            raise ValueError('--list is read-only and cannot be combined with --resolve-deps')
        if args.resolve_deps:
            subprocess.run(['lake', 'resolve-deps'], cwd=root, check=True)
        modules = mathlib_cache_roots(root, imports)
        if args.lint_runtime:
            driver = root / '.lake/packages/mathlib/scripts/lint-style.lean'
            modules = sorted(set(modules) | {name for name in lean_imports(driver.read_text())
                                             if name.startswith(('Mathlib.', 'Batteries.'))})
        if not modules:
            raise ValueError('No cache inputs; refusing an unscoped cache download')
        if args.list:
            print('\n'.join(modules))
            return 0
        command = ['lake', 'exe', 'cache', 'get', *modules]
        if args.guarded:
            prefix = (family(root) or 'lean_tools').upper() + '_VERIFY_DIR'
            selected = os.environ.get(prefix)
            stamp = datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
            receipt = (Path(selected + '-cache.json') if selected else
                       root / '.lake/verification' / ('cache-' + stamp + '-' + str(os.getpid()) + '.json')).resolve()
            if receipt.exists():
                raise ValueError('Use a fresh cache receipt path')
            return run(root, command, receipt)
        subprocess.run(command, cwd=root, check=True)
        return 0
    except subprocess.CalledProcessError as error:
        return error.returncode if error.returncode >= 0 else 128 - error.returncode
    except (OSError, ValueError) as error:
        print('Cache acquisition failed: ' + str(error), file=sys.stderr)
        return 2
