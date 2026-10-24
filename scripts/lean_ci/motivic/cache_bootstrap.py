#!/usr/bin/env python3
# Authors: kangxyz
"""Run focused Mathlib cache acquisition with the pinned bootstrap resource caps."""
import argparse
from pathlib import Path
import re
import subprocess
import sys

LEAF = re.compile(r"(?:Mathlib|Batteries)(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def validate_command(command: list[str], root: Path) -> None:
    if command[:4] != ['lake', 'exe', 'cache', 'get'] or len(command) == 4:
        raise ValueError('Cache bootstrap requires lake exe cache get with explicit leaf roots')
    for name in command[4:]:
        if LEAF.fullmatch(name) is None:
            raise ValueError('Cache bootstrap requires explicit Mathlib./Batteries. module leaves')
        package = 'mathlib' if name.startswith('Mathlib.') else 'batteries'
        path = root / '.lake/packages' / package / Path(*name.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise ValueError(f'Missing focused cache source: {name}')


def run(root: Path, command: list[str], receipt: Path) -> int:
    validate_command(command, root)
    from ..cli import main as native_main
    from . import resource_config, runtime_environment
    return native_main(['run', '--root', str(root), '--receipt', str(receipt),
                        '--bootstrap-cache', '--', *command],
                       resource_config=resource_config(), environment=runtime_environment())


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    try:
        return run(args.root.resolve(), command, args.receipt)
    except (OSError, ValueError, ImportError, subprocess.SubprocessError) as error:
        print(f'Focused cache bootstrap failed: {error}', file=sys.stderr)
        return 125


if __name__ == '__main__':
    raise SystemExit(main())
