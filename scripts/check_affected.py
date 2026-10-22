#!/usr/bin/env python3
"""Run Aglib's native build, source, Test, lint and axiom checks."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))


def main(argv=None):
    from lean_ci.cli import main as native_main
    from lean_ci.resources import ResourceConfig
    arguments = ['check', *(sys.argv[1:] if argv is None else argv)]
    return native_main(arguments, root=ROOT, production=('Aglib',),
                       source_checks=[
                           [sys.executable, 'scripts/check_library_layout.py'],
                           [sys.executable, 'scripts/check_placeholders.py'],
                           [sys.executable, 'scripts/check_source_policy.py']],
                       resource_config=ResourceConfig(prefix='AGLIB',
                           profile_keys=('R5_LEAN_REMOTE_PROFILE',)))


if __name__ == '__main__':
    raise SystemExit(main())
