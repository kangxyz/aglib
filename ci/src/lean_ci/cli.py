"""Run a committed repository policy with the reusable CI lifecycle."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

from .application import Application, git
from .execution.state import TemporalInputs, digest


def load_application(root, adapter_path=None, *, local=False, config_path=None):
    root = Path(root).resolve()
    if config_path is not None:
        if adapter_path is not None:
            raise ValueError('Select a common configuration or a legacy adapter, not both')
        from .configured import create_application
        config_path = Path(config_path)
        if config_path.is_absolute():
            config_path = config_path.relative_to(root)
        return create_application(root, config_path.as_posix())
    path = (root / adapter_path).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        raise ValueError('Adapter must be a committed Python file inside the repository')
    relative = path.relative_to(root).as_posix()
    observations = TemporalInputs() if local else None
    if local:
        observations.hash_file(path)
    if not local and git(root, 'status', '--porcelain', '--untracked-files=all').strip():
        raise ValueError('Repository adapter requires clean committed source')
    if not local:
        git(root, 'ls-files', '--error-unmatch', '--', relative)
    if not local and git(root, 'show', 'HEAD:' + relative) != path.read_bytes():
        raise ValueError('Repository adapter bytes differ from committed source')
    # Never create an untracked bytecode directory while loading repository policy.
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        name = '_lean_ci_adapter_' + digest(str(path))
        spec = importlib.util.spec_from_file_location(name, path)
        if spec is None or spec.loader is None:
            raise ValueError('Could not load repository adapter')
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
        application = module.create_application(root)
    finally:
        sys.dont_write_bytecode = previous
    if not isinstance(application, Application) or application.root != root:
        raise ValueError('Adapter must return Application for its committed repository root')
    if local:
        # Include actually loaded repository policy code before any selector is
        # called; working-tree admission never waives actual tooling identity.
        for loaded in list(sys.modules.values()):
            filename = getattr(loaded, '__file__', None)
            if filename:
                loaded_path = Path(filename).resolve()
                if loaded_path.is_relative_to(root) and loaded_path.suffix == '.py' and loaded_path.is_file():
                    observations.hash_file(loaded_path)
        observations.assert_stable()
        application._local_loader_observations = observations
    return application


def main(argv=None, application=None):
    effective_argv = list(sys.argv[1:] if argv is None else argv)
    if effective_argv[:1] == ['execute']:
        if application is not None:
            raise ValueError('Frozen execution loads only its admitted synchronized request')
        from .transport.frozen import main as execute_main
        return execute_main(effective_argv[1:])
    if effective_argv[:1] == ['replay']:
        if application is not None:
            raise ValueError('Kernel replay uses its explicit common configuration')
        from .checks.replay import main as replay_main
        return replay_main(effective_argv[1:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['plan', 'source', 'native', 'finalize', 'check', 'prepare', 'scope', 'request', 'imports'])
    parser.add_argument('--adapter', type=Path)
    parser.add_argument('--config', type=Path)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--state', type=Path)
    parser.add_argument('--repository')
    parser.add_argument('--default-branch', default='main')
    parser.add_argument('--head')
    parser.add_argument('--requested-base')
    parser.add_argument('--target', action='append', default=[])
    parser.add_argument('--github-output', type=Path)
    parser.add_argument('--progress', type=Path)
    parser.add_argument('--outputs', type=Path)
    parser.add_argument('--bundle', type=Path)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args(effective_argv)
    try:
        if application is None:
            config = args.config or (Path('.github/lean-ci.toml') if args.adapter is None else None)
            application = load_application(args.root or Path.cwd(), args.adapter,
                                           local=args.phase in ('check', 'prepare'), config_path=config)
        elif args.adapter is not None or args.config is not None or (args.root and args.root.resolve() != application.root):
            raise ValueError('A supplied Application already fixes its adapter and root')
        effective_config = getattr(application.adapter, 'config_path', '.github/lean-ci.toml')
        if args.phase not in ('check', 'prepare', 'scope', 'request', 'imports') and args.state is None:
            raise ValueError('Committed CI phases require --state')
        if (args.write or args.check) and args.phase != 'imports':
            raise ValueError('--write/--check apply only to import-file maintenance')
        if args.phase == 'imports':
            if args.adapter is not None or (args.write and args.check):
                raise ValueError('Import maintenance uses one configuration and one action')
            from .project.imports import maintain
            result = maintain(application.root, effective_config, write=args.write)
            print(json.dumps(result, indent=2))
            if result['changed'] and not args.write:
                return 1
        elif args.phase == 'scope':
            if args.adapter is not None:
                raise ValueError('Scope inspection requires a common configuration')
            from .project.configuration import load_config
            from .project.scope import select_scope
            config = load_config(application.root, effective_config)
            result = select_scope(application.root, config, base=args.requested_base, targets=args.target)
            print(json.dumps(result, indent=2))
        elif args.phase == 'request':
            if args.adapter is not None or args.bundle is None:
                raise ValueError('A common native request requires --bundle and a configuration')
            from .transport.request import create_request
            print(json.dumps(create_request(application.root, effective_config,
                             args.requested_base, args.target, bundle=args.bundle), indent=2))
        elif args.phase == 'prepare':
            if args.adapter is not None:
                raise ValueError('Shared preparation requires a common configuration')
            from .execution.prepare import prepare
            from .execution.state import read_json, write_json
            scope = None
            if args.state:
                plan = read_json(args.state / 'plan.json')
                application.validate_plan(plan)
                scope = plan['scope']
            result = prepare(application.root, effective_config,
                             args.requested_base, args.target, scope=scope,
                             directory=args.state / 'prepare' if args.state else None)
            if args.state:
                write_json(args.state / 'prepare.json', result)
            print(json.dumps(result, indent=2))
        elif args.phase == 'check':
            print(json.dumps(application.check(args.state, args.requested_base, args.target,
                                               args.progress, args.outputs), indent=2))
        elif args.phase == 'plan':
            if not args.repository or not args.head:
                raise ValueError('Planning requires --repository and exact --head')
            plan = application.plan(args.repository, args.default_branch, args.head, args.state,
                                    args.requested_base)
            if args.github_output:
                scope = plan.get('scope', {})
                with args.github_output.open('a') as output:
                    for key in ('native', 'publish'):
                        if key in scope:
                            if type(scope[key]) is not bool:
                                raise ValueError('Workflow output must be boolean: ' + key)
                            output.write(key + '=' + str(scope[key]).lower() + '\n')
            print(json.dumps({'plan_id': plan['id'], 'head': plan['head'],
                              'required_phases': plan['required_phases']}, sort_keys=True))
        elif args.phase == 'finalize':
            result = application.finalize(args.state, args.outputs)
            if args.github_output:
                with args.github_output.open('a') as output:
                    output.write('mappings=' + str(bool(args.outputs and args.outputs.is_file())).lower() + '\n')
            print(json.dumps(result, indent=2))
        else:
            application.run_phase(args.state, args.phase, args.progress)
        return 0
    except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError) as error:
        print('CI core failed closed: ' + str(error), file=sys.stderr)
        return 1
