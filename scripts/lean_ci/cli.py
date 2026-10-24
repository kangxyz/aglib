"""One entry point for native Lean work and the libraries' source tools."""
import argparse
import importlib
import json
import os
from pathlib import Path
import sys
import tempfile
import tomllib

from . import __version__, build, local, resources

LIBRARIES = {'Aglib': 'aglib', 'quillen-k-theory': 'quillen', 'Motivic': 'motivic'}


def package_options(root):
    lakefile = root / 'lakefile.toml'
    package = tomllib.loads(lakefile.read_text()) if lakefile.is_file() else {}
    family = LIBRARIES.get(package.get('name'))
    return (importlib.import_module('.' + family, __package__).options(root)
            if family else {'production': tuple(package.get('defaultTargets', ()))})


def run_command(args, package, config, environment):
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        raise ValueError('run requires a command after --')
    if args.bootstrap_cache:
        if command[:4] != ['lake', 'exe', 'cache', 'get']:
            raise ValueError('--bootstrap-cache requires lake exe cache get [MODULE...]')
        for name in command[4:]:
            if not name.startswith(('Mathlib.', 'Batteries.')):
                raise ValueError('Scoped cache roots must name Mathlib or Batteries modules')
            from .source import module_path
            module_path(name)
    budget = resources.limits(environment, config=config)
    if args.bootstrap_cache and not budget.get('remote_profile'):
        budget['max_active_lean'] = None
    if args.bootstrap_cache or args.capped_toolchain:
        threads = (1 if args.bootstrap_cache and not budget.get('remote_profile') else
                   build.build_threads(environment, config))
        with build.capped_toolchain(package, threads, environment=environment, config=config) as env:
            bounded = command if args.bootstrap_cache else resources.capped_command(command, env, config)
            return resources.run(bounded, cwd=package, receipt=args.receipt,
                                 budget=budget, env=env, config=config)
    return resources.run(command, cwd=package, receipt=args.receipt,
                         budget=budget, env=environment, config=config)


def main(argv=None, *, root=None, production=(), check_targets=(), source_checks=None,
         resource_config=None, environment=None):
    arguments = list(sys.argv[1:] if argv is None else argv)
    if arguments[:1] and arguments[0] in LIBRARIES.values():
        return importlib.import_module('.' + arguments[0], __package__).main(arguments[1:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--version', action='version', version='lean-incremental-ci ' + __version__)
    sub = parser.add_subparsers(dest='action', required=True)
    check = sub.add_parser('check', help='native CI checks with compatible successes retained')
    compile_ = sub.add_parser('build', help='incremental native build or no-build mapping export')
    run = sub.add_parser('run', help='one command using the existing resource implementation')
    for command in (check, compile_, run):
        command.add_argument('--root', type=Path, default=Path(root or '.'))
    for command in (check, compile_):
        command.add_argument('--state', '--receipt-dir', dest='state', type=Path)
        command.add_argument('--outputs', '--native-outputs', type=Path)
        command.add_argument('--rehash', action='store_true', help='native builds always rehash')
    check.add_argument('--production', action='append', default=[])
    check.add_argument('--check-target', action='append', default=[])
    check.add_argument('--base')
    check.add_argument('--head')
    check.add_argument('--full', action='store_true')
    check.add_argument('--source-only', action='store_true')
    check.add_argument('--progress', type=Path)
    check.add_argument('--list', action='store_true', help='print native commands without executing')
    check.add_argument('--ci', action='store_true', help=argparse.SUPPRESS)
    compile_.add_argument('--export-only', '--no-build', action='store_true')
    compile_.add_argument('--selection', choices=('module', 'library'), default='module')
    compile_.add_argument('targets', nargs='+')
    run.add_argument('--receipt', type=Path, required=True)
    run.add_argument('--bootstrap-cache', action='store_true')
    run.add_argument('--capped-toolchain', action='store_true')
    run.add_argument('command', nargs=argparse.REMAINDER)
    for family in LIBRARIES.values():
        sub.add_parser(family, help=family.capitalize() + ' source, generation and cache tools')
    args = parser.parse_args(arguments)
    package = args.root.resolve()
    try:
        defaults = package_options(package)
        config = resource_config or defaults.get('resource_config') or resources.ResourceConfig(
            profile_keys=('R5_LEAN_REMOTE_PROFILE',))
        env = dict(os.environ if environment is None else environment)
        if environment is None and defaults.get('environment') is not None:
            env = dict(defaults['environment'])
        if args.action == 'run':
            return run_command(args, package, config, env)
        if args.action == 'check':
            roots = args.production or list(production) or list(defaults.get('production', ()))
            if not roots:
                raise ValueError('At least one production root is required')
            extras = [*(check_targets or defaults.get('check_targets', ())), *args.check_target]
            checks = defaults.get('source_checks', ()) if source_checks is None else source_checks
            if args.source_only and not checks:
                raise ValueError('No source policy is configured for this package')
            if args.list:
                for command in local.commands(package, roots, extras, checks):
                    print(json.dumps(command))
                return 0
            result = local.check(package, roots, check_targets=extras, source_checks=checks,
                base=args.base, head=args.head, full=args.full, source_only=args.source_only,
                progress=args.progress, state=args.state, outputs=args.outputs,
                resource_config=config, environment=env)
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        state = args.state or Path(tempfile.mkdtemp(prefix='lean-native-build-'))
        if not args.export_only:
            return build.build(package, args.targets, state.resolve(), rehash=True,
                outputs=args.outputs, config=config, environment=env, selection=args.selection)
        if args.outputs is None:
            raise ValueError('--export-only requires --outputs')
        state.mkdir(parents=True, exist_ok=True)
        args.outputs.parent.mkdir(parents=True, exist_ok=True)
        with build.capped_toolchain(package, build.build_threads(env, config),
                                   environment=env, config=config) as bounded:
            return resources.run(['lake', '--rehash', '--no-build', 'build',
                *build.native_targets(args.targets, args.selection), '-o', str(args.outputs.resolve())],
                cwd=package, env=bounded, receipt=state / 'export.json', config=config)
    except (OSError, ValueError, KeyError, ImportError) as error:
        print('Native Lean command failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
