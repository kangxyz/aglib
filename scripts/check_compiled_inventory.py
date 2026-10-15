#!/usr/bin/env python3
"""Require the scoped replay view to match current source; reject stale project oleans.

This checks only project-prefixed files in the package's build root. The integrator
must also preserve exact package-prefix search-path ownership for leanchecker.
"""
import argparse
from pathlib import Path
import sys
from library_sources import audit_sources, source_modules, test_modules

ROOT = Path(__file__).resolve().parents[1]


def check_inventory(root: Path) -> list[str]:
    library = root / '.lake/build/lib/lean'
    expected = source_modules(root) | test_modules(root) | {
        path for path in audit_sources(root) if path == Path('AglibTest/AuditSupport.lean')}
    actual = {path.relative_to(library).with_suffix('.lean')
              for prefix in ['Aglib', 'AglibTest']
              for path in (library / prefix).rglob('*.olean')}
    actual |= {Path(name + '.lean') for name in ['Aglib', 'AglibTest']
               if (library / (name + '.olean')).is_file()}
    # Negative controls are intentionally compiled separately, not part of the
    # trusted positive source inventory or the selected kernel replay prefixes.
    negatives = {path for path in actual if 'NegativeControls' in path.parts}
    errors = []
    # Compare actual entry spelling: AGLib and Aglib alias on case-insensitive hosts.
    entries = {path.name: path for path in library.iterdir()} if library.is_dir() else {}
    for prefix in ['AGLib', 'AGLibTest', 'AlgebraicGeometry', 'AlgebraicGeometryTest',
                   'R5Lab', 'Quillen']:
        old_file = entries.get(prefix + '.olean')
        old_directory = entries.get(prefix)
        if old_file is not None or (old_directory is not None
                                      and any(old_directory.rglob('*.olean'))):
            errors.append(f'Old project-prefix compiled artifacts remain: {prefix}')
    if negatives:
        errors.append('Negative control oleans occupy the kernel replay view: '
                      + ', '.join(map(str, sorted(negatives))))
    if missing := expected - actual:
        errors.append('Missing compiled project source: ' + ', '.join(map(str, sorted(missing))))
    if stale := actual - expected - negatives:
        errors.append('Stale compiled project source: ' + ', '.join(map(str, sorted(stale))))
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    errors = check_inventory(args.root)
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print('Compiled project inventory matches current positive source and audit support.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
