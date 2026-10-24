"""Library-specific Quillen policy and cache commands for the shared toolkit."""
from pathlib import Path
import sys


def resource_config():
    from ..resources import ResourceConfig
    return ResourceConfig(prefix='QUILLEN', profile_keys=('R5_LEAN_REMOTE_PROFILE',),
                          memory_keys=('AGLIB_LEAN_MEMORY_MB',), rss_keys=('AGLIB_RSS_LIMIT_MB',),
                          build_thread_keys=('AGLIB_BUILD_THREADS',))


def options(root):
    from ..local import SourceCheck
    directory = Path(__file__).resolve().parent
    common = (directory / '__init__.py', directory / 'library_sources.py',
              directory.parent / 'source.py', directory.parent / 'cli.py', directory.parent / '__main__.py')
    source_roots = (Path(root) / 'examples' / 'downstream',)
    return dict(production=('Quillen',), check_targets=(), resource_config=resource_config(),
                source_checks=tuple(SourceCheck(
                    (sys.executable, str(Path(__file__).resolve().parents[1] / '__main__.py'), 'quillen', action, '--root', str(root)),
                    (*common, *(directory / name for name in files)), source_roots)
                    for action, files in (
                        ('layout', ('check_library_layout.py', 'generate_imports.py')),
                        ('placeholders', ('check_placeholders.py',)))))


def main(argv=None):
    import argparse
    from importlib import import_module
    commands = {'layout': 'check_library_layout', 'placeholders': 'check_placeholders',
                'imports': 'generate_imports', 'cache-sources': 'cache_sources', 'cache': 'cache'}
    arguments = list(sys.argv[1:] if argv is None else argv)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=commands)
    if not arguments or arguments[0] not in commands:
        parser.parse_args(arguments)
    return import_module('.' + commands[arguments[0]], __name__).main(arguments[1:])
