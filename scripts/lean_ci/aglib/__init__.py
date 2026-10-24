"""Aglib source policy and migration inspection inside the shared toolkit."""
from pathlib import Path
import sys


def options(root):
    from ..local import SourceCheck
    from ..resources import ResourceConfig
    directory = Path(__file__).parent
    common = (directory / '__init__.py', directory / 'sources.py', directory.parent / 'source.py', directory.parent / 'cli.py', directory.parent / '__main__.py')
    return dict(production=('Aglib',), check_targets=(),
        source_checks=tuple(SourceCheck(
            (sys.executable, str(Path(__file__).resolve().parents[1] / '__main__.py'), 'aglib', name, '--root', str(root)),
            (*common, directory / (name + '.py'))) for name in ('layout', 'placeholders', 'policy')),
        resource_config=ResourceConfig(prefix='AGLIB', profile_keys=('R5_LEAN_REMOTE_PROFILE',)))


def main(argv):
    if not argv or argv[0] in ('--help', '-h'):
        print('Usage: lean-ci aglib {layout,placeholders,policy,imports} [OPTIONS]', file=sys.stderr)
        return 0 if argv else 2
    action, *arguments = argv
    if action in ('layout', 'imports'):
        from .layout import main
    elif action == 'placeholders':
        from .placeholders import main
    elif action == 'policy':
        from .policy import main
    else:
        print('Unknown Aglib tool: ' + action, file=sys.stderr)
        return 2
    return main(arguments)
