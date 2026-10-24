#!/usr/bin/env python3
# Authors: kangxyz
"""Build the independent client with this checkout's locked dependencies and guard."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib

ROOT = Path.cwd()


def prepare(root: Path) -> Path:
    """Prepare an explicitly requested client; preserve existing cache ownership."""
    client = root / 'examples/downstream'
    config = tomllib.loads((client / 'lakefile.toml').read_text())
    if not (client / 'MotivicClient.lean').is_file():
        raise ValueError('Missing independent MotivicClient source')
    if (client / 'lean-toolchain').read_bytes() != (root / 'lean-toolchain').read_bytes():
        raise ValueError('Client and library must use the same pinned Lean toolchain')
    requirements = config.get('require', [])
    if not any(row.get('name') == 'Motivic' and row.get('path') == '../..'
               for row in requirements):
        raise ValueError('Expected the client to require this Motivic checkout by ../..')
    packages = root / '.lake/packages'
    if not packages.is_dir():
        raise ValueError('Resolve the root pinned dependencies before building the client')
    cache = client / '.lake'
    if cache.is_symlink() or (cache / 'build').is_symlink():
        raise ValueError('Client .lake and build outputs must be owned directories, not symlinks')
    link = cache / 'packages'
    if link.is_symlink():
        if link.resolve() != packages.resolve():
            raise ValueError('Client packages must refer to this checkout, not a foreign cache')
    elif link.exists():
        raise ValueError('Preserve and reconcile existing client packages before using the shared cache')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    if manifest['name'] != 'Motivic':
        raise ValueError('Expected the Motivic root dependency manifest')
    for package in manifest['packages']:
        package['inherited'] = True
    manifest['packages'].append({'type': 'path', 'name': 'Motivic', 'scope': '',
        'dir': '../..', 'inherited': False, 'configFile': 'lakefile.toml',
        'manifestFile': 'lake-manifest.json'})
    manifest['name'] = config['name']
    manifest['lakeDir'] = '.lake'
    cache.mkdir(exist_ok=True)
    if not link.is_symlink():
        link.symlink_to(Path('../../../.lake/packages'), target_is_directory=True)
    (client / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return client



def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--receipt-dir', type=Path)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
    receipts = args.receipt_dir or Path('.lake/verification') / ('client-' + stamp)
    if not receipts.is_absolute():
        receipts = root / receipts
    try:
        from . import resource_config, runtime_environment
        from lean_ci.build import build
        client = prepare(root)
        return build(client, ['MotivicClient'], receipts, rehash=True,
                     config=resource_config(), environment=runtime_environment(), selection='module')
    except (OSError, ValueError) as error:
        print(f'Independent client build failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
