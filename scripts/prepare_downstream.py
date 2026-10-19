#!/usr/bin/env python3
"""Prepare the independent client with pinned inherited dependencies, without network.

Only client manifest/cache setup is written. No dependency source or cache is mutated.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def manifest_bytes(root: Path) -> bytes:
    """Compute the canonical client manifest without changing source or caches."""
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        package['inherited'] = True
    manifest['packages'].append({'type': 'path', 'name': manifest['name'],
        'scope': '', 'dir': '../..', 'inherited': False,
        'configFile': 'lakefile.toml', 'manifestFile': 'lake-manifest.json'})
    manifest['name'] = '«aglib-downstream»'
    manifest['lakeDir'] = '.lake'
    return (json.dumps(manifest, indent=2) + '\n').encode()


def prepare(root: Path) -> None:
    client = root / 'examples/downstream'
    target = client / 'lake-manifest.json'
    prepared = manifest_bytes(root)
    # This file is tracked. Even a byte-identical write changes its temporal
    # identity and invalidates the enclosing committed-source CI guard.
    if not target.is_file() or target.read_bytes() != prepared:
        target.write_bytes(prepared)
    cache = client / '.lake'
    cache.mkdir(exist_ok=True)
    link = cache / 'packages'
    if not link.exists() and not link.is_symlink():
        link.symlink_to(Path('../../../.lake/packages'), target_is_directory=True)


def main() -> int:
    prepare(ROOT)
    print('Independent downstream manifest prepared from the root pinned dependency manifest.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
