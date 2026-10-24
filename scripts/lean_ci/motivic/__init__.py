# Authors: kangxyz
"""Motivic policy and explicit helper commands for the shared Lean toolkit."""
import importlib
import os
from pathlib import Path
import sys


def resource_config():
    from ..resources import ResourceConfig
    return ResourceConfig(prefix='MOTIVIC', profile_keys=('R5_LEAN_REMOTE_PROFILE', 'AGLIB_REMOTE_PROFILE'),
                          memory_keys=('AGLIB_LEAN_MEMORY_MB',), rss_keys=('AGLIB_RSS_LIMIT_MB',),
                          build_thread_keys=('AGLIB_BUILD_THREADS',))


def runtime_environment():
    environment = dict(os.environ)
    for suffix in ('BUILD_THREADS', 'LEAN_MEMORY_MB', 'RSS_LIMIT_MB'):
        if 'MOTIVIC_' + suffix in environment:
            environment['AGLIB_' + suffix] = environment['MOTIVIC_' + suffix]
    return environment


def options(root):
    from ..local import SourceCheck
    directory = Path(__file__).resolve().parent
    inputs = tuple(directory / name for name in ('__init__.py', 'repository.py', 'imports.py', 'sources.py'))
    return dict(production=('Motivic',), check_targets=(),
                source_checks=(SourceCheck((sys.executable, str(Path(__file__).resolve().parents[1] / '__main__.py'), 'motivic',
                                            'repository', '--root', str(root)),
                                           (*inputs, directory.parent / 'source.py', directory.parent / 'cli.py', directory.parent / '__main__.py')),),
                resource_config=resource_config(), environment=runtime_environment())


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    actions = {'repository': 'repository', 'imports': 'imports', 'cache': 'cache',
               'cache-bootstrap': 'cache_bootstrap', 'build': 'build',
               'client': 'client'}
    if not argv or argv[0] in ('-h', '--help'):
        print('Motivic actions: ' + ', '.join(actions))
        return 0 if argv else 2
    action = argv.pop(0)
    if action not in actions:
        print('Unknown Motivic action: ' + action, file=sys.stderr)
        return 2
    return importlib.import_module('.' + actions[action], __name__).main(argv)
