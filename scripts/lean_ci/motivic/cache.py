#!/usr/bin/env python3
# Authors: kangxyz
"""Fetch only reachable Mathlib cache roots for explicit local Lean targets."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import subprocess
import sys

from .sources import lean_imports, module_path

ROOT = Path.cwd()


def cache_roots(root: Path, targets: list[str]) -> list[str]:
    pending = list(targets)
    visited, modules = set(), set()
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        prefix = name.split('.')[0]
        if prefix == 'Mathlib':
            if name == 'Mathlib':
                raise ValueError('Whole Mathlib imports are not a focused cache input')
            modules.add(name)
            continue
        if prefix in {'Motivic', 'MotivicTest'}:
            path = root / module_path(name)
        elif prefix == 'Aglib':
            path = root / '.lake/packages/Aglib' / module_path(name)
        else:
            # Lean/Std and dependency support libraries are not Mathlib cache roots.
            continue
        if not path.is_file():
            raise ValueError(f'Missing reachable source: {path}; resolve pinned dependencies first')
        pending.extend(lean_imports(path.read_text()))
    if not modules:
        raise ValueError('No reachable Mathlib imports; refusing an unscoped cache download')
    return sorted(modules)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--list', action='store_true', help='print cache roots without running Lake')
    parser.add_argument('--resolve-deps', action='store_true', help='resolve the existing pinned manifest first')
    parser.add_argument('--lint-runtime', action='store_true',
                        help='also fetch exact Mathlib/Batteries imports of the pinned text-style driver')
    parser.add_argument('--guarded', action='store_true', help='use the reviewed Aglib resource guard')
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        for target in args.targets:
            if target.split('.')[0] not in {'Motivic', 'MotivicTest'} or not (
                    root / module_path(target)).is_file():
                raise ValueError(f'Expected an existing local Motivic/MotivicTest target: {target}')
        if args.list and args.resolve_deps:
            raise ValueError('--list is read-only and cannot be combined with --resolve-deps')
        if args.resolve_deps:
            subprocess.run(['lake', 'resolve-deps'], cwd=root, check=True)
        modules = cache_roots(root, args.targets)
        if args.lint_runtime:
            driver = root / '.lake/packages/mathlib/scripts/lint-style.lean'
            # Lean/Lake are installed; Cli and ImportGraph use the isolated runtime overlay.
            modules = sorted(set(modules) | {name for name in lean_imports(driver.read_text())
                                             if name.startswith(('Mathlib.', 'Batteries.'))})
        if args.list:
            print('\n'.join(modules))
        else:
            argv = ['lake', 'exe', 'cache', 'get', *modules]
            from . import runtime_environment
            environment = runtime_environment()
            if args.guarded:
                from .cache_bootstrap import run
                stamp = datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
                receipt = root / '.lake/verification' / ('cache-' + stamp + '.json')
                return run(root, argv, receipt)
            subprocess.run(argv, cwd=root, env=environment, check=True)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'Focused cache setup failed: {error}', file=sys.stderr)
        return getattr(error, 'returncode', 1)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
