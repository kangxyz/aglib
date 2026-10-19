"""Run a committed repository policy with the reusable CI lifecycle."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

from .engine import Application, git
from .state import digest


def load_application(root, adapter_path):
    root = Path(root).resolve()
    path = (root / adapter_path).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        raise ValueError('Adapter must be a committed Python file inside the repository')
    relative = path.relative_to(root).as_posix()
    if git(root, 'status', '--porcelain', '--untracked-files=all').strip():
        raise ValueError('Repository adapter requires clean committed source')
    git(root, 'ls-files', '--error-unmatch', '--', relative)
    if git(root, 'show', 'HEAD:' + relative) != path.read_bytes():
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
    return application


def main(argv=None, application=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['plan', 'source', 'native', 'finalize'])
    parser.add_argument('--adapter', type=Path)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--repository')
    parser.add_argument('--default-branch', default='main')
    parser.add_argument('--head')
    parser.add_argument('--requested-base')
    parser.add_argument('--github-output', type=Path)
    parser.add_argument('--progress', type=Path)
    parser.add_argument('--outputs', type=Path)
    args = parser.parse_args(argv)
    try:
        if application is None:
            if args.adapter is None:
                raise ValueError('A committed --adapter is required')
            application = load_application(args.root or Path.cwd(), args.adapter)
        elif args.adapter is not None or (args.root and args.root.resolve() != application.root):
            raise ValueError('A supplied Application already fixes its adapter and root')
        if args.phase == 'plan':
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
            print(json.dumps(application.finalize(args.state, args.outputs), indent=2))
        else:
            application.run_phase(args.state, args.phase, args.progress)
        return 0
    except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError) as error:
        print('CI core failed closed: ' + str(error), file=sys.stderr)
        return 1
