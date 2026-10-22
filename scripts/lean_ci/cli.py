"""Run native Lake commands locally or inside an already owned remote phase."""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile
import tomllib

from . import build, local, resources


def main(argv=None, *, root=None, production=(), check_targets=(), source_checks=(),
         resource_config=None, environment=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    check = sub.add_parser('check', help='native final checks with compatible successes retained')
    compile_ = sub.add_parser('build', help='incremental native module build or no-build mapping export')
    for command in (check, compile_):
        command.add_argument('--root', type=Path, default=Path(root or '.'))
        command.add_argument('--state', '--receipt-dir', dest='state', type=Path)
        command.add_argument('--outputs', '--native-outputs', type=Path)
        command.add_argument('--rehash', action='store_true', help='compatibility: native builds always rehash')
    check.add_argument('--production', action='append', default=[])
    check.add_argument('--check-target', action='append', default=[])
    check.add_argument('--base')
    check.add_argument('--head')
    check.add_argument('--full', action='store_true')
    check.add_argument('--source-only', action='store_true')
    check.add_argument('--progress', type=Path)
    check.add_argument('--list', action='store_true', help='print native commands without executing them')
    check.add_argument('--ci', action='store_true', help=argparse.SUPPRESS)
    compile_.add_argument('--export-only', '--no-build', action='store_true')
    compile_.add_argument('--selection', choices=('module', 'library'), default='module')
    compile_.add_argument('targets', nargs='+')
    args = parser.parse_args(argv)
    package = args.root.resolve()
    config = resource_config or resources.ResourceConfig(profile_keys=('R5_LEAN_REMOTE_PROFILE',))
    environment = dict(os.environ if environment is None else environment)
    try:
        if args.action == 'check':
            roots = args.production or list(production)
            if not roots:
                lakefile = package / 'lakefile.toml'
                if lakefile.is_file():
                    roots = tomllib.loads(lakefile.read_text()).get('defaultTargets', [])
            extras = [*check_targets, *args.check_target]
            if args.list:
                for command in local.commands(package, roots, extras, source_checks):
                    print(json.dumps(command))
                return 0
            summary = local.check(package, roots, check_targets=extras, source_checks=source_checks,
                                  base=args.base, head=args.head, full=args.full, source_only=args.source_only,
                                  progress=args.progress, state=args.state, outputs=args.outputs,
                                  resource_config=config, environment=environment)
            print(json.dumps(summary, indent=2, sort_keys=True))
            return 0
        state = args.state or Path(tempfile.mkdtemp(prefix='lean-native-build-'))
        if not args.export_only:
            return build.build(package, args.targets, state.resolve(), rehash=True,
                               outputs=args.outputs, config=config, environment=environment,
                               selection=args.selection)
        if args.outputs is None:
            raise ValueError('--export-only requires --outputs')
        state.mkdir(parents=True, exist_ok=True)
        args.outputs.parent.mkdir(parents=True, exist_ok=True)
        with build.capped_toolchain(package, build.build_threads(environment, config),
                                   environment=environment, config=config) as bounded:
            return resources.run(['lake', '--rehash', '--no-build', 'build',
                                  *build.native_targets(args.targets, args.selection), '-o',
                                  str(args.outputs.resolve())], cwd=package, env=bounded,
                                 receipt=state / 'export.json', config=config)
    except (OSError, ValueError, KeyError) as error:
        print('Native Lean command failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
