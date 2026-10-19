#!/usr/bin/env python3
"""Run pinned Batteries checks on exact selected defining-module origins."""
import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DRIVER = Path('.lake/packages/batteries/scripts/runLinter.lean')
MARKER = '    let decls ← getDeclsInPackage module.getRoot\n'
EXACT = '''    let lintEnv ← getEnv
    let decls ← getDeclsInPackage module.getRoot
    let decls := decls.filter fun name =>
      match lintEnv.getModuleIdxFor? name with
      | some index => lintEnv.header.moduleNames[index.toNat]! == module
      | none => false
'''


def selected_driver(source):
    if source.count(MARKER) != 1:
        raise ValueError('Unrecognized pinned Batteries declaration enumeration')
    # Keep the same slow/default/always linters, nolints, formatting and failure
    # semantics. Only the defining-module selection changes.
    return source.replace(MARKER, EXACT)


def run(root, modules):
    if not modules:
        raise ValueError('Exact declaration lint requires a nonempty module selection')
    source = selected_driver((root / DRIVER).read_text())
    with tempfile.TemporaryDirectory(prefix='aglib-declaration-runtime-') as temporary:
        driver = Path(temporary) / 'SelectedLinter.lean'
        driver.write_text(source)
        # Release each imported environment before checking the next origin.
        for module in modules:
            result = subprocess.run(['lake', 'env', os.environ.get('LEAN') or 'lean',
                                     '--run', str(driver), '--no-build', module], cwd=root)
            if result.returncode:
                return result.returncode
        return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    args = parser.parse_args()
    try:
        return run(ROOT, args.modules)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print('Selected declaration lint failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
