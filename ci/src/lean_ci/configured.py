"""Declarative policy adapter over Application and the existing native recipe."""
from pathlib import Path
import json
import sys

from .project.configuration import lean_files, load_config
from .application import Application
from .execution.recipe import native_recipe
from .project.scope import BUILD_INPUTS, changed_paths, local_base, select_scope
from .project.source import lean_imports
from .execution.state import check_binding, digest, file_hash

POLICY_INPUTS = {'source': ('exceptions', 'budget', 'controls', 'dependencies', 'style', 'inventory'),
    'style': ('style',), 'declarations': ('nolints',),
    'builtin': (), 'axioms': ('axioms', 'private_generated'),
    'inventory': ('private_generated',), 'controls': ('controls',),
    'expected-failure': ('controls',)}


def create_application(root, config_path='.github/lean-ci.toml'):
    root = Path(root).resolve()
    config = load_config(root, config_path)
    return Application(root, ConfiguredAdapter(config_path, config=config), package_cwd=root / config['package_dir'])


class ConfiguredAdapter:
    cache_implementation_owners = ('execution/runner.py', 'execution/state.py', 'execution/runtime.py',
                                   'execution/resources.py', 'execution/build.py', 'execution/batch.py')

    def __init__(self, config_path='.github/lean-ci.toml', *, config=None):
        self.config_path = config_path
        self._config = config

    def config(self, root, *, refresh=False):
        if self._config is None or refresh:
            self._config = load_config(root, self.config_path)
        return self._config

    def plan(self, root, repository, default_branch, head, requested_base=None, api=None):
        from .transport.history import select_baseline
        from .project.dependencies import DependencySourcesUnavailable, resolve_planning_sources
        config = self.config(root)
        baseline = select_baseline(root, repository, default_branch, head,
            requested_base=requested_base, api=api, config=config)
        if not isinstance(baseline, dict) or baseline.get('kind') not in {'verified', 'initial'}:
            raise ValueError('History returned no verified/initial coverage decision')
        if baseline['kind'] == 'verified' and not baseline.get('base'):
            raise ValueError('Verified history decision omitted its accepted base')
        if baseline['kind'] == 'initial' and baseline.get('base') is not None:
            raise ValueError('Initialization cannot invent an accepted baseline')
        try:
            scope = select_scope(root, config, base=baseline.get('base'), head=head,
                                 initial=baseline['kind'] == 'initial')
        except DependencySourcesUnavailable:
            # A fresh hosted runner has no Lake checkout yet. Obtain exact Git
            # sources before authoritative selection; no compiler is needed.
            resolve_planning_sources(root, config, baseline.get('base'))
            scope = select_scope(root, config, base=baseline.get('base'), head=head,
                                 initial=baseline['kind'] == 'initial')
        return {'baseline': baseline, 'scope': scope, 'configuration': digest(config)}

    def required_phases(self, root, payload):
        return ['source', 'native'] if payload['scope']['native'] else ['source']

    def validate_plan(self, root, plan):
        config = self.config(root, refresh=True)
        baseline = plan['baseline']
        expected = select_scope(root, config, base=baseline.get('base'), head=plan['head'],
                                 initial=baseline['kind'] == 'initial')
        if plan.get('configuration') != digest(config) or plan.get('scope') != expected:
            raise ValueError('Configured scope no longer matches its current inputs')

    def local_inputs(self, root, requested_base=None, targets=()):
        config = self.config(root)
        paths = {self.config_path, '.gitignore', '.gitmodules'}
        paths.update(p for p in changed_paths(root, local_base(root, requested_base)) if p.endswith('.md'))
        for workspace in config['workspaces']:
            package = Path(workspace['path'])
            paths.update((package / name).as_posix() for name in (*BUILD_INPUTS, '.gitignore'))
        for values in config['policy'].values():
            paths.update(values)
        paths.update(row['path'] for row in config['modules'].values())
        paths.update(row['path'] for row in config['extra_sources'])
        # Directory enrollment guards new/deleted candidates without observing
        # build caches. Overlap is intentional: names and bytes have distinct roles.
        directories = []
        for workspace in config['workspaces']:
            package = Path(root) / workspace['path']
            for directory in [package, *sorted({p.parent for p in lean_files(package)})]:
                if '.git' in directory.relative_to(root).parts:
                    continue
                directories.append({'path': directory.relative_to(root).as_posix(),
                                    'exclude': sorted(p.name for p in directory.iterdir() if p.is_dir())})
        return sorted(paths) + directories

    def select_scope(self, root, requested_base=None, targets=(), source_basis=None):
        if not source_basis or source_basis.get('kind') != 'working-tree':
            raise ValueError('Local configured checks require a working-tree source basis')
        config = self.config(root)
        return {'scope': select_scope(root, config, base=requested_base, targets=targets),
                'configuration': digest(config)}

    def validate_local(self, root, plan):
        config = self.config(root, refresh=True)
        expected = select_scope(root, config, base=plan['scope']['base'], targets=plan['scope']['requested_targets'])
        if plan.get('configuration') != digest(config) or plan.get('scope') != expected:
            raise ValueError('Local configured scope drifted')

    def _check(self, root, config, kind, *, origins=(), workspace=None, paths=()):
        workspace = workspace or config['workspaces'][0]
        package = Path(root) / workspace['path']
        names = [config['modules'][n]['module'] for n in origins]
        command = [sys.executable, '-P', '-m', 'lean_ci.checks.native', kind, '--root', str(package),
                   '--config', str(Path(root) / self.config_path), '--modules', *names]
        identifier = workspace['id'] + '/' + kind + '/' + (origins[0] if origins else 'sources')
        task = {'id': identifier, 'kind': 'check', 'check_kind': kind, 'command': command,
                'cwd': str(package), 'modules': names, 'origins': list(origins),
                'workspace': workspace['id'], 'raw_paths': list(paths),
                'native': kind != 'source', 'capped': kind != 'source'}
        if kind == 'source':
            task['input_boundary'] = 'common-' + kind
        if kind == 'source':
            task['modules'] = []
            task['raw_paths'] = [row['path'] for row in config['modules'].values()] + [
                row['path'] for row in config['extra_sources']]
        if kind == 'style':
            # Text checks read source bytes, never a subject's native artifacts.
            task['modules'] = []
        if kind == 'builtin':
            task['command'] = ['lake', '--no-build', 'lint', '--builtin-only', *names]
        return task

    def tasks(self, root, plan, phase, directory):
        config, scope = self.config(root), plan['scope']
        root_workspace = config['workspaces'][0]
        def selection_file(task, selection, label):
            index = task['command'].index('--modules')
            task['command'][index:] = ['--selection-json', str(Path(directory) / (label + '.json'))]
            task['generated'] = json.dumps(selection)
            task['generated_argument_index'] = index + 1
            return task

        source = [selection_file(self._check(root, config, 'source'), scope['source_check'], 'source-selection')]
        markdown = [p for p in scope['changed'] if p.endswith('.md') and (Path(root) / p).is_file()]
        for path in markdown:
            source[0]['command'] += ['--changed-path', path]
        source[0]['raw_paths'] += markdown
        styles = []
        for workspace in config['workspaces']:
            origins = [n for n in scope['source_style'] if config['modules'][n]['workspace'] == workspace['id']]
            if origins:
                from .checks.native import module_components
                task = self._check(root, config, 'style', origins=origins, workspace=workspace,
                    paths=[config['modules'][n]['path'] for n in origins])
                styles.append(selection_file(task, [module_components(config['modules'][n]['module']) for n in origins], workspace['id'] + '-style-selection'))
        source_before = styles if phase != 'source' else []
        prepare = []
        if phase != 'source':
            for workspace in config['workspaces']:
                if any(t['workspace'] == workspace['id'] for t in styles):
                    prepare.append({'id': workspace['id'] + '/style-environment', 'kind': 'environment',
                        'cwd': str(Path(root) / workspace['path']),
                        'command': ['lake', 'env', 'printenv', 'LEAN_PATH'],
                        'environment_output': str(Path(directory) / (workspace['id'] + '-style-search.txt'))})
        universe = set(scope['declarations'])

        def checks(origins, workspace):
            result = [self._check(root, config, 'builtin', origins=origins, workspace=workspace)] if origins else []
            for name in origins:
                if name in universe:
                    kinds = ('declarations', 'inventory') if config['modules'][name]['role'] in {'diagnostics', 'formal_only'} else ('declarations', 'axioms')
                    for kind in kinds:
                        task = self._check(root, config, kind, origins=[name], workspace=workspace)
                        if kind == 'axioms':
                            task['covers'] = ['axioms', 'inventory']
                        result.append(task)
            result.sort(key=lambda t: ('builtin', 'declarations', 'axioms', 'inventory').index(t['check_kind']))
            for task in result:
                if task['check_kind'] in {'declarations', 'axioms', 'inventory'}:
                    task['check_batch'] = {'id': task['check_kind'] + '-' + workspace['id'] + '-' + digest(origins),
                        'mode': 'canonical-prefix', 'read_only': True, 'single_process': True}
            return result

        def group(identifier, origins, workspace, before=()):
            if not origins and not before:
                return None
            return {'id': identifier, 'cwd': workspace['path'],
                    'modules': [config['modules'][n]['module'] for n in origins],
                    'selection': 'module', 'before': list(before), 'checks': checks(origins, workspace)}

        providers = group('providers', scope['providers'], root_workspace, source_before)
        consumers = group('consumers', scope['consumers'], root_workspace)
        clients = []
        auxiliary = group('auxiliary', scope.get('auxiliary', []), root_workspace)
        if auxiliary:
            clients.append(auxiliary)
        tests = group('tests', scope['tests'], root_workspace)
        if tests:
            clients.append(tests)
        for workspace in config['clients']:
            item = group('client-' + workspace['id'], scope['clients'].get(workspace['id'], []), workspace)
            if item:
                clients.append(item)
        for workspace in config['workspaces']:
            selected_checks = []
            for kind, names in scope.get('check_only', {}).items():
                for name in names:
                    if config['modules'][name]['workspace'] == workspace['id']:
                        task = self._check(root, config, kind, origins=[name], workspace=workspace)
                        if kind in {'declarations', 'axioms', 'inventory'}:
                            task['check_batch'] = {'id': 'policy-' + kind + '-' + workspace['id'],
                                'mode': 'canonical-prefix', 'read_only': True, 'single_process': True}
                        if kind == 'axioms':
                            task['covers'] = ['axioms', 'inventory']
                        if kind == 'inventory' and name in scope.get('check_only', {}).get('axioms', []):
                            continue
                        selected_checks.append(task)
            if selected_checks:
                clients.append({'id': 'policy-' + workspace['id'], 'cwd': workspace['path'],
                                'modules': [], 'build': False, 'checks': selected_checks})
        for kind, path in [('expected-failure', p) for p in scope['expected_failure']]:
            row = next((r for r in config['modules'].values() if r['path'] == path), None)
            workspace = next(w for w in config['workspaces'] if w['id'] == (row['workspace'] if row else 'root'))
            task = self._check(root, config, kind, workspace=workspace, paths=[path])
            # Compile-failure fixtures remain exact files, outside positive groups.
            task['command'][-1:] = ['--selection-json', str(Path(directory) / ('negative-' + digest(path) + '.json'))]
            task['generated'] = json.dumps([str(Path(root) / path)])
            task['generated_argument_index'] = -1
            task['id'] = kind + '/' + path
            clients.append({'id': task['id'], 'cwd': workspace['path'], 'modules': [], 'checks': [task]})
        if scope.get('common_controls') or scope.get('controls'):
            paths = list(scope.get('controls', []))
            task = self._check(root, config, 'controls', paths=paths)
            task['id'] = 'common/controls'
            task['command'][-1:] = ['--selection-json', str(Path(directory) / 'controls.json')]
            task['generated'] = json.dumps([str(Path(root) / p) for p in paths])
            task['generated_argument_index'] = -1
            clients.append({'id': 'controls', 'cwd': root_workspace['path'], 'modules': [], 'checks': [task]})
        if not scope['native']:
            return native_recipe(root, directory, source_checks=source, phase='source')
        exports = [g['id'] for g in [providers, consumers, *clients] if g and g.get('modules') and g.get('build', True)]
        return native_recipe(root, directory, source_checks=source, prepare=prepare, provider_gate=providers,
                             root_workspace=consumers, clients=clients, exports=exports, phase=phase)

    def binding(self, root, task, toolchain, reflection=None, observations=None):
        from .checks.native import checker_inputs, runtime_roots
        config = self.config(root)
        package = Path(task['cwd'])
        kind = task['check_kind']
        hash_file = observations.hash_file if observations else file_hash
        policy = [path for category in POLICY_INPUTS[kind] for path in config['policy'].get(category, [])]
        policy += [(Path(task['cwd']) / name).as_posix() for name in BUILD_INPUTS]
        raw = [str(Path(root) / path) for path in [*policy, *task.get('raw_paths', ())]]
        source = kind in {'source', 'style', 'expected-failure', 'controls'}
        if not source:
            raw += [str(Path(root) / config['modules'][name]['path']) for name in task['origins']]
        control_sources = set(task.get('raw_paths', ())) if kind in {'expected-failure', 'controls'} else set()
        if kind in {'expected-failure', 'controls'}:
            for path in config['policy']['controls']:
                profile = json.loads((Path(root) / path).read_text())
                for entry in profile.get('expected_failures', []):
                    if isinstance(entry, dict) and entry.get('path') in control_sources:
                        control_sources.update(entry.get('prerequisites', []))
            raw += [str(Path(root) / p) for p in control_sources]
        if kind != 'builtin':
            raw.append(sys.executable)
            raw += [str(p) for p in checker_inputs(kind, root=package)]
        if kind == 'source':
            raw.append(str(Path(__file__).resolve().parent / 'project/configuration.py'))
        roots = list(runtime_roots(kind))
        modules = [] if source else task['modules']
        arguments = list(task['command'])
        if task.get('generated'):
            arguments[task.get('generated_argument_index', -1)] = '<selection-json>'
        value = check_binding(package, kind, modules, arguments, [], raw_paths=raw,
                              generated=digest(task['generated']) if task.get('generated') else None,
                              toolchain=toolchain, hash_file=hash_file)
        reflection_roots = [*roots, *([] if source else task['modules'])]
        if kind in {'expected-failure', 'controls'}:
            overlay_origins = {row['module'] for row in config['modules'].values() if row['path'] in control_sources}
            reflection_roots += [name for path in control_sources for name in lean_imports((Path(root) / path).read_text()) if name not in overlay_origins]
            reflection_roots.append('Init')
        value['reflective_imports'] = reflection.closure(reflection_roots) if reflection and reflection_roots else None
        value['covers'] = task.get('covers', [kind])
        value['predicate'] = 'common-runtime-first-exact-origin-v1' if kind == 'declarations' else 'common-' + kind + '-v1'
        if kind == 'source':
            # Source enrollment is semantic configuration; per-origin native
            # predicates bind only their own relevant policy data above.
            value['enrollment'] = config
            from .checks.guards import markdown_link_targets
            markdown = [p for p in task.get('raw_paths', ()) if p.endswith('.md')]
            targets = []
            for candidate in markdown_link_targets(root, markdown):
                path = Path(root) / candidate
                if observations:
                    observations.observe_resolution(path)
                targets.append({'path': candidate, 'resolved': path.resolve().relative_to(Path(root).resolve()).as_posix(),
                                'kind': 'directory' if path.is_dir() else 'file' if path.is_file() else 'missing'})
            value['markdown_targets'] = targets
        return value

    def summary(self, root, plan, records):
        return {'scope': plan['scope'], 'coverage_kind': plan['scope']['coverage'],
                'initialization': 'closed-current-universe' if plan['scope']['initial'] else 'verified-baseline-delta',
                'formal_acceptance': 'separately-required-at-mathematical-adoption'}

    def local_summary(self, root, plan, record):
        return {'scope': plan['scope'], 'coverage_kind': plan['scope']['coverage'],
                'formal_acceptance': 'separately-required-at-mathematical-adoption'}
