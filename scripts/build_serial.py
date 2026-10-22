#!/usr/bin/env python3
"""Compatibility command for one guarded native incremental module build."""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))


def main(argv=None):
    from lean_ci.build import build
    from lean_ci.resources import ResourceConfig
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--receipt-dir', type=Path, required=True)
    parser.add_argument('--rehash', action='store_true')
    parser.add_argument('--outputs', type=Path)
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args(argv)
    return build(args.root.resolve(), args.targets, args.receipt_dir,
                 rehash=args.rehash, outputs=args.outputs, selection='module',
                 config=ResourceConfig(prefix='AGLIB',
                     profile_keys=('R5_LEAN_REMOTE_PROFILE',)))


if __name__ == '__main__':
    raise SystemExit(main())
