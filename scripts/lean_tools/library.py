"""Library data and dispatch for the single shared Lean development workflow."""
import importlib
import os
from pathlib import Path
import sys
import tomllib

LIBRARIES = {'Aglib': 'aglib', 'quillen-k-theory': 'quillen', 'Motivic': 'motivic'}
PROFILES = {
    'aglib': dict(production='Aglib', inventory='sources.py',
        checks=(('layout', ('layout.py',)), ('placeholders', ('placeholders.py',)),
                ('policy', ('policy.py',))),
        commands={'layout': 'layout', 'imports': 'layout', 'placeholders': 'placeholders', 'policy': 'policy'}),
    'quillen': dict(production='Quillen', inventory='library_sources.py',
        checks=(('layout', ('check_library_layout.py', 'generate_imports.py')),
                ('placeholders', ('check_placeholders.py',))),
        commands={'layout': 'check_library_layout', 'placeholders': 'check_placeholders',
                  'imports': 'generate_imports'}),
    'motivic': dict(production='Motivic', inventory='sources.py',
        checks=(('repository', ('repository.py', 'imports.py')),),
        commands={'repository': 'repository', 'imports': 'imports', 'build': 'build', 'client': 'client'}),
}


def configuration(root):
    path = Path(root) / 'lakefile.toml'
    return tomllib.loads(path.read_text()) if path.is_file() else {}


def family(root):
    return LIBRARIES.get(configuration(root).get('name'))


def local_roots(root):
    selected = family(root)
    names = ((PROFILES[selected]['production'],) if selected else
             tuple(configuration(root).get('defaultTargets', ())))
    return tuple(dict.fromkeys(name for base in names for name in (base, base + 'Test')))


def resource_config(selected):
    from .resources import ResourceConfig
    aliases = selected in ('quillen', 'motivic')
    return ResourceConfig(prefix=selected.upper(),
        profile_keys=('R5_LEAN_REMOTE_PROFILE',) + (('AGLIB_REMOTE_PROFILE',) if selected == 'motivic' else ()),
        memory_keys=('AGLIB_LEAN_MEMORY_MB',) if aliases else (),
        rss_keys=('AGLIB_RSS_LIMIT_MB',) if aliases else (),
        build_thread_keys=('AGLIB_BUILD_THREADS',) if aliases else ())


def runtime_environment(selected):
    environment = dict(os.environ)
    if selected == 'motivic':
        for suffix in ('BUILD_THREADS', 'LEAN_MEMORY_MB', 'RSS_LIMIT_MB'):
            if 'MOTIVIC_' + suffix in environment:
                environment['AGLIB_' + suffix] = environment['MOTIVIC_' + suffix]
    return environment


def options(root):
    from .local import SourceCheck
    selected = family(root)
    if selected is None:
        return {'production': tuple(configuration(root).get('defaultTargets', ()))}
    profile = PROFILES[selected]
    package = Path(__file__).resolve().parent
    directory = package / selected
    common = (directory / '__init__.py', directory / profile['inventory'],
              package / 'source.py', package / 'cli.py', package / '__main__.py', Path(__file__).resolve())
    roots = (Path(root) / 'examples/downstream',) if selected == 'quillen' else ()
    result = dict(production=(profile['production'],), check_targets=(),
        resource_config=resource_config(selected),
        source_checks=tuple(SourceCheck(
            (sys.executable, str(package / '__main__.py'), selected, action, '--root', str(root)),
            (*common, *(directory / name for name in files)), roots)
            for action, files in profile['checks']))
    if selected == 'motivic':
        result['environment'] = runtime_environment(selected)
    return result


def main(selected, argv):
    commands = PROFILES[selected]['commands']
    if not argv or argv[0] in ('-h', '--help'):
        print('Usage: lean-tools ' + selected + ' {' + ','.join(commands) + ',cache} [OPTIONS]')
        return 0 if argv else 2
    action, *arguments = argv
    if action in ('cache', 'cache-sources', 'cache-bootstrap'):
        from . import cache
        return (cache.bootstrap_main(arguments) if action == 'cache-bootstrap' else
                cache.main((['--list'] if action == 'cache-sources' else []) + arguments))
    if action not in commands:
        print('Unknown library tool: ' + action, file=sys.stderr)
        return 2
    return importlib.import_module('.' + selected + '.' + commands[action], __package__).main(arguments)
