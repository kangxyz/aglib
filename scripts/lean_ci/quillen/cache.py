"""Acquire only enumerated Mathlib cache roots using the installed guard."""
import argparse
import datetime
import os
from pathlib import Path
import subprocess
import sys

from .cache_sources import workspace_imports, mathlib_cache_roots


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--ci', action='store_true')
    parser.add_argument('targets', nargs='*')
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        imports = workspace_imports(root, args.targets)
        resolved = subprocess.run(['lake', 'resolve-deps'], cwd=root, stdout=sys.stderr)
        if resolved.returncode:
            return resolved.returncode if resolved.returncode > 0 else 128 - resolved.returncode
        modules = mathlib_cache_roots(root, imports)
        if not modules:
            raise ValueError('No cache inputs were produced')
        if not args.ci:
            result = subprocess.run(['lake', 'exe', 'cache', 'get', *modules], cwd=root)
            return result.returncode if result.returncode >= 0 else 128 - result.returncode
        stamp = datetime.datetime.now().strftime('%Y%m%d-%H%M%S')
        receipt = Path(os.environ.get('QUILLEN_VERIFY_DIR',
            str(root / '.lake/verification' / f'cache-{stamp}-{os.getpid()}')) + '-cache.json').resolve()
        if receipt.exists():
            raise ValueError('Use a fresh QUILLEN_VERIFY_DIR for each cache/check invocation.')
        from ..cli import main as native_main
        code = native_main(['run', '--root', str(root), '--receipt', str(receipt),
                            '--bootstrap-cache', '--', 'lake', 'exe', 'cache', 'get', *modules])
        if receipt.is_file():
            print(receipt.read_text())
        return code
    except (OSError, ValueError) as error:
        print('Cache acquisition failed: ' + str(error), file=sys.stderr)
        return 2
