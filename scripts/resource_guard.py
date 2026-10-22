#!/usr/bin/env python3
"""Compatibility command for the shared native resource guard."""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))


def main(argv=None):
    from lean_ci import build, resources
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--bootstrap-cache', action='store_true')
    parser.add_argument('--capped-toolchain', action='store_true')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('a command after -- is required')
    if args.bootstrap_cache and command != ['lake', 'exe', 'cache', 'get']:
        parser.error('--bootstrap-cache permits only exact lake exe cache get')
    config = resources.ResourceConfig(prefix='AGLIB',
                                      profile_keys=('R5_LEAN_REMOTE_PROFILE',))
    budget = resources.limits(config=config)
    if args.bootstrap_cache and not budget.get('remote_profile'):
        budget['max_active_lean'] = None
    if args.bootstrap_cache or args.capped_toolchain:
        threads = (1 if args.bootstrap_cache and not budget.get('remote_profile') else
                   build.build_threads(config=config))
        with build.capped_toolchain(Path.cwd(), threads=threads, config=config) as env:
            bounded = command if args.bootstrap_cache else resources.capped_command(command, env, config)
            return resources.run(bounded, receipt=args.receipt, budget=budget, env=env, config=config)
    return resources.run(command, receipt=args.receipt, budget=budget, config=config)


if __name__ == '__main__':
    raise SystemExit(main())
