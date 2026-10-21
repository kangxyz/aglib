#!/usr/bin/env python3
"""Plan, execute, and independently finalize committed incremental CI coverage."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'ci'))

from lean_ci.build import source_order
from lean_ci.cli import main as generic_main
from lean_ci.engine import Application, SCHEMA, git, source_files
from lean_ci.resources import ResourceConfig
from lean_ci.runtime import NativeRuntime, parse_search_path
from lean_ci.recipe import native_recipe

import affected_scope
import ci_baseline
from ci_audit import AUDIT_DRIVER, AUDIT_DRIVER_SHA256, audit_command
from check_affected import check_links
from ci_state import (Progress, ReflectionGraph, ReflectionUnavailable, TemporalInputs, check_binding, digest, file_hash, read_json,
                      module_identity, valid_receipt, valid_success, write_json)
from library_sources import lean_imports, module_path
from prepare_downstream import manifest_bytes


PACKAGE_SOURCES = ['ci/lean_ci/' + name + '.py' for name in
                   ('__init__', '__main__', 'source', 'state', 'github', 'engine', 'runtime', 'resources', 'build', 'cli',
                    'execution', 'local', 'recipe', 'mappings', 'frozen', 'batch')]
# These reviewed dependencies remain bound through this existing recipe owner.
# Historical core recipes retain their original ordered owner list.
FIXED_AUDIT_SOURCES = {
    'scripts/ci_audit.py': '9fecbd4d662923288fe3722356c75d4835e2feff40c3a860af41ee97470bb8c3',
    AUDIT_DRIVER: AUDIT_DRIVER_SHA256,
}
OLD_AUDIT_GENERATOR_BLOB = '682dedef7a8286e327360a39d8d86b6ce3828188'
OLD_AUDIT_SOURCE_BLOBS = {
    'AglibTest/Axioms.lean': 'd5386546e73bea1d24a81b66836aa5a074db65e9',
    'AglibTest/AuditSupport.lean': 'cfd2df7050a8c4388f1626bda2e5085df3c52e58',
    'AglibTest/AuditCoverage.lean': '675bbb041fa7148aea8331afc03cc78b527cf6a3',
}
AUDIT_COVERAGE_DOCUMENTATION = {
    'before': '675bbb041fa7148aea8331afc03cc78b527cf6a3',
    'after': 'd8d7f048a2a3eeed6f1193ba2be976f248ce6221',
}
POLICY = ['scripts/ci_pipeline.py', 'scripts/ci_state.py', 'scripts/resource_guard.py',
          'scripts/build_serial.py', 'scripts/library_sources.py',
          'scripts/run_declaration_linter.py', 'scripts/run_style_linter.py',
          'scripts/check_negative_controls.py', 'scripts/nolints.json', 'scripts/nolints-style.txt', 'AglibTest/AuditSupport.lean',
          'AglibTest/AuditCoverage.lean', 'Audits/Aglib.lean',
          *FIXED_AUDIT_SOURCES, *PACKAGE_SOURCES, *sorted(affected_scope.CONFIG)]
DRIVERS = ['.lake/packages/batteries/scripts/runLinter.lean',
           '.lake/packages/mathlib/scripts/lint-style.lean']
GENERATED_MANIFEST = 'examples/downstream/lake-manifest.json'
SEMANTIC_POLICY = ('scripts/run_declaration_linter.py', 'scripts/run_style_linter.py',
                   'scripts/check_compiled_inventory.py', 'scripts/nolints.json',
                   'scripts/nolints-style.txt', 'Audits/Aglib.lean',
                   'AglibTest/AuditSupport.lean', 'AglibTest/AuditCoverage.lean',
                   *FIXED_AUDIT_SOURCES)
LEGACY_CUTOVER = 'cc17eecf0344f15c89ffc04cade60b1b09cf9f43'
# This is a retained-legacy-policy contract, NOT per-leaf linter equivalence.
# The exact old recipe checked production declarations in the Aglib umbrella
# environment; it did not declaration-lint AglibTest or AuditSupport.
LEGACY_RECIPE = 'b6ff3fa21884ff965e54a942af37ae622d23c06a'
CUTOVER_ADAPTERS = {
    'scripts/run_declaration_linter.py': (None, '28e13cab4e7629028e9e4bf17be5f71451d123aa'),
    'scripts/run_style_linter.py': ('e6f94c66feda3507d00b1fea1d6377a73dba54f6',
                                    '90a8e4fbdb7b749a2ef849387972c6d523aed474'),
    'scripts/check_compiled_inventory.py': ('135ccc581cf005f0644ee92db526c686f463bfa1',
                                          '67bf9ce6a5d4b33c2c6463383853198f9050519b'),
}


def tree(root, revision):
    result = {}
    for entry in git(root, 'ls-tree', '-rz', '--full-tree', revision).split(b'\0'):
        if entry:
            metadata, path = entry.split(b'\t', 1)
            mode, kind, object_id = metadata.decode().split()
            if kind != 'blob':
                raise ValueError('Unsupported committed source entry: ' + path.decode())
            result[path.decode()] = {'mode': mode, 'blob': object_id}
    return result


def mathematical_tree(root, revision):
    return {p: value for p, value in tree(root, revision).items()
            if (p.endswith('.lean') and not p.startswith('ci/')) or p in affected_scope.CONFIG}


def validate_fixed_audit_sources(root):
    for path, expected in FIXED_AUDIT_SOURCES.items():
        if file_hash(root / path) != expected:
            raise ValueError('Native semantic policy changed: unreviewed fixed audit source ' + path)


def native_policy(root, baseline, scope, before, current):
    """No changed semantic check may silently inherit an older predicate.

    Unknown global policy changes need a dedicated category migration, rather
    than a guessed small selection or an implicit whole-library rebuild.
    """
    old, new = tree(root, baseline['verified_base']), tree(root, scope['head'])
    validate_fixed_audit_sources(root)
    changed = [p for p in SEMANTIC_POLICY if old.get(p) != new.get(p)]
    if scope.get('configuration_update'):
        return {'mode': 'fresh-current-checks-after-configuration-update',
                'inputs': {p: new.get(p) for p in SEMANTIC_POLICY},
                'changed_local_predicates': changed,
                'upstream_predicates': 'actual resolved driver/runtime bytes bound at execution; exact-key reuse only',
                'legacy_inheritance': 'none for affected check universe'}
    if not changed:
        return {'mode': 'unchanged-semantic-check-policy',
                'inputs': {p: new.get(p) for p in SEMANTIC_POLICY}}
    coverage_path = 'AglibTest/AuditCoverage.lean'
    if (changed == [coverage_path]
            and old.get(coverage_path) == {'mode': '100644', 'blob': AUDIT_COVERAGE_DOCUMENTATION['before']}
            and new.get(coverage_path) == {'mode': '100644', 'blob': AUDIT_COVERAGE_DOCUMENTATION['after']}):
        return {'mode': 'reviewed-audit-coverage-documentation',
                'witness_commit': baseline['verified_base'], 'witness_run': baseline['run_id'],
                'source_blobs': AUDIT_COVERAGE_DOCUMENTATION,
                'equivalence': 'two docstrings only; declaration types, values, origin names and '
                               'axiom/private/generated controls unchanged',
                'current_checks': 'full origin audit and fresh rejection controls remain required'}
    fixed_audit_migration = (
        set(changed) == set(FIXED_AUDIT_SOURCES)
        and old.get('scripts/ci_pipeline.py', {}).get('blob') == OLD_AUDIT_GENERATOR_BLOB
        and all(old.get(path) == {'mode': '100644', 'blob': expected}
                for path, expected in OLD_AUDIT_SOURCE_BLOBS.items())
        and all(old.get(path) is None and new.get(path, {}).get('mode') == '100644'
                for path in FIXED_AUDIT_SOURCES))
    if fixed_audit_migration:
        return {'mode': 'reviewed-fixed-audit-entrypoint-migration',
                'witness_commit': baseline['verified_base'], 'witness_run': baseline['run_id'],
                'old_generator_blob': OLD_AUDIT_GENERATOR_BLOB,
                'old_audit_source_blobs': OLD_AUDIT_SOURCE_BLOBS,
                'fixed_audit_sources': FIXED_AUDIT_SOURCES,
                'equivalence': 'same selected import sequence, visibility, frontend options/trust, '
                               'origin audit and private/generated controls; selection is data',
                'inherited_coverage': 'unchanged audit predicate under the verified ancestor policy'}
    def blob(entries, path):
        entry = entries.get(path)
        if entry is not None and entry['mode'] != '100644':
            return 'unsupported-mode'
        return entry['blob'] if entry else None
    known_cutover = (baseline['verified_base'] == LEGACY_CUTOVER
                     and old.get('scripts/check.sh', {}).get('blob') == LEGACY_RECIPE
                     and all(p in CUTOVER_ADAPTERS and
                             (blob(old, p), blob(new, p)) == CUTOVER_ADAPTERS[p]
                             for p in changed)
                     and all(before.get(p) == current.get(p) for p in affected_scope.CONFIG))
    if not known_cutover:
        raise ValueError('Native semantic policy changed; assign and validate its affected check '
                         'category before inheriting coverage (no automatic broad rebuild): '
                         + ', '.join(changed))
    # The selector follows both old and new import edges. Excluding its full
    # affected closure, plus requiring identical source/pins, bounds retention
    # to unchanged local import closures under the exact legacy recipe.
    affected = set(scope['providers'] + scope['consumers'] + scope['tests'])
    def enrolled(root_name):
        text = git(root, 'show', LEGACY_CUTOVER + ':' + root_name + '.lean').decode()
        return set(lean_imports(text))
    production, tests = enrolled('Aglib'), enrolled('AglibTest')
    unchanged = {affected_scope.node(p) for p in before if p.endswith('.lean')
                 and before[p] == current.get(p)} - affected
    inherited_production = sorted(production & unchanged)
    inherited_tests = sorted(tests & unchanged)
    return {'mode': 'explicit-retained-legacy-policy-cutover',
            'witness_commit': LEGACY_CUTOVER, 'witness_run': baseline['run_id'],
            'legacy_recipe_blob': LEGACY_RECIPE,
            'policy_inputs': {p: {'before': old.get(p), 'current': new.get(p)} for p in SEMANTIC_POLICY},
            'unchanged_production_origins': inherited_production,
            'unchanged_test_origins': inherited_tests,
            'origin_digest': digest([inherited_production, inherited_tests]),
            'production_declaration_policy': 'legacy Aglib umbrella environment; not current per-leaf equivalence',
            'test_policy': 'legacy build/builtin/style/trust; no inherited Batteries declaration check',
            'current_checks': 'every new, changed or affected selected origin; no success-record re-keying'}


def normalized_scope(root, scope):
    scope = json.loads(json.dumps(scope))
    # prepare_downstream owns this deterministic manifest, tracked in Aglib.
    # Its input is the committed root manifest, never an independently trusted pin.
    if GENERATED_MANIFEST not in tree(root, 'HEAD'):
        scope['identity'].pop(GENERATED_MANIFEST, None)
    return scope


def assert_native_scope(root, scope, base_math, head_math, changed):
    """A second, source-based gate against accidentally empty/omitted math scope."""
    math_changed = {p for p in base_math.keys() | head_math.keys()
                    if base_math.get(p) != head_math.get(p)}
    controls_changed = affected_scope.controls_changed(changed)
    if not scope['native'] and (math_changed or controls_changed or scope['controls']):
        raise ValueError('Changed mathematical/control inputs cannot have source-only native coverage')
    selected = set(scope['providers'] + scope['consumers'] + scope['tests'])
    if scope.get('configuration_update'):
        required = {affected_scope.node(p) for p in head_math if p.endswith('.lean')
                    and (p.startswith(('Aglib/', 'AglibTest/', 'Tools/')) or p in {'Aglib.lean', 'AglibTest.lean'})
                    and p not in {'Audits/Aglib.lean', 'AglibTest/AuditSupport.lean'}
                    and not p.startswith(('AglibTest/NegativeControls/', 'examples/downstream/'))}
        if required - selected or not (scope['trust'] and scope['controls'] and scope['client_audit']):
            raise ValueError('Configuration update omitted complete current check scope')
    for path in sorted(math_changed):
        if path in affected_scope.CONFIG:
            if not scope.get('configuration_update'):
                raise ValueError('Configuration/pin changes need an explicit validated migration scope: ' + path)
            continue
        if path.startswith('examples/downstream/'):
            if not scope['client_audit']:
                raise ValueError('Changed client mathematical input omitted from native audit scope: ' + path)
        elif path.startswith('AglibTest/NegativeControls/'):
            if not scope['controls'] or not scope['trust']:
                raise ValueError('Changed rejection control omitted from native scope: ' + path)
        elif path in {'Audits/Aglib.lean', 'AglibTest/AuditSupport.lean'}:
            if not scope['trust']:
                raise ValueError('Changed audit policy omitted from native scope: ' + path)
        elif path in head_math and affected_scope.node(path) not in selected:
            raise ValueError('Changed mathematical module omitted from native scope: ' + path)
    if controls_changed and not (scope['native'] and scope['trust'] and scope['controls']):
        raise ValueError('Changed control/runtime policy requires fresh native rejection controls')


def runtime_imports(root):
    imports = set()
    for path in DRIVERS:
        imports.update(n for n in lean_imports((root / path).read_text())
                       if n.startswith(('Batteries.', 'Mathlib.', 'Cli.', 'ImportGraph.')))
    return sorted(imports)


def declaration_policy(scope):
    return {'production': 'full Aglib umbrella environment',
            'tests': 'full AglibTest umbrella environment',
            'support': 'exact AuditSupport origin when selected',
            'equivalence': 'umbrella and exact-origin environments are distinct predicates'}


def tasks(root, plan, phase, directory, *, phases=None):
    """One library policy recipe for committed CI and local final validation."""
    scope = plan['scope']
    selected_phases = set(phases or ['providers', 'provider-lint', 'consumers', 'trust', 'client'])
    complete = selected_phases == {'providers', 'provider-lint', 'consumers', 'trust', 'client'}
    def task(name, args, kind='process', cwd=root, **extra):
        return {'id': name, 'kind': kind, 'command': list(map(str, args)),
                'cwd': str(cwd), **extra}
    def safe(name, args, cwd=root, **extra):
        return task(name, args, cwd=cwd, capped=True, **extra)
    source_checks = [task(script, ['python3', 'scripts/' + script]
                     + (['--check'] if script == 'generate_imports.py' else []))
                     for script in ['generate_imports.py', 'check_library_layout.py',
                                    'check_placeholders.py', 'check_source_policy.py']]
    source_checks.append(task('links', [], kind='links'))
    source_checks.extend(task('tooling/' + test, ['python3', '-m', 'unittest', 'discover', '-s',
                         '.github/actions/lake-cache' if test == 'native-cache' else
                         'ci' if test == 'lean-ci' else 'scripts', '-p',
                         'test_*.py' if test in ('native-cache', 'lean-ci') else test + '.py'])
                         for test in scope['tooling_tests'])
    if phase == 'source' or (phase == 'check' and not scope['native']):
        return native_recipe(root, directory, source_checks=source_checks, phase='source')
    if phase not in ('native', 'check') or not scope['native']:
        raise ValueError('Native phase was not required by this selection')
    prepare = []
    core_changed = any(path.startswith('ci/') or path in {
        'scripts/ci_pipeline.py', 'scripts/ci_state.py', 'scripts/ci_baseline.py',
        '.github/workflows/ci.yml', 'lean-toolchain', 'examples/downstream/lean-toolchain',
    } for path in scope['changed'])
    if core_changed and complete:
        prepare.append(task('core-native-cache', ['python3', 'ci/native_test.py', '--state',
                            directory / 'core-cache-fixture', '--resource-prefix', 'AGLIB',
                            '--profile-key', 'R5_LEAN_REMOTE_PROFILE']))
    client = root / 'examples/downstream'
    prepare.append(task('prepare-client', ['python3', 'scripts/prepare_downstream.py'],
                        establishes_inputs=True))
    lake = ['lake', '--rehash']
    imports = runtime_imports(root) if selected_phases & {'provider-lint', 'consumers'} else []
    graph_roots = list(dict.fromkeys(['Aglib', 'AglibTest',
                        *scope['providers'], *scope['consumers'], *scope['tests'],
                        *(['AglibTest.AuditSupport', 'AglibTest.AuditCoverage'] if scope['trust'] else [])]))
    if selected_phases == {'providers'}:
        graph_roots = list(scope['providers'])
    current_modules = source_order(root, graph_roots)
    selected = set(scope['providers'] + scope['consumers'] + scope['tests'])
    if scope['trust']:
        selected.update(['AglibTest.AuditSupport', 'AglibTest.AuditCoverage'])
    unrelated = sorted(set(current_modules) - selected)
    before = ([safe('unrelated-cached-imports', lake + ['--no-build', 'build', *unrelated])]
              if unrelated else [])
    build_graph = bool(selected_phases & {'providers', 'consumers'})
    # A category repair consumes a cache-validated graph, without compiling a
    # second graph solely to repeat a previously completed check category.
    graph = (safe('shared-root-build', lake + ['build', *graph_roots, *('+' + n for n in imports)],
                  kind='graph-build', modules=current_modules) if build_graph else
             safe('shared-root-cached', lake + ['--no-build', 'build', *graph_roots]))
    checks = []
    lint_lake = ['lake', '--no-build']
    def full_lint(name, module, category):
        command = (lint_lake + ['lint', '--builtin-only', module] if category == 'builtin' else
                   ['lake', 'env', 'lean', '--run', DRIVERS[0], '--no-build', module])
        return safe(name, command, kind='check', check_kind=category,
                    modules=[module], selection=[module])
    def exact_lint(prefix, names):
        return [check for index, name in enumerate(names)
                for check in [full_lint(f'{prefix}/builtin/{index}', name, 'builtin'),
                              safe(f'{prefix}/declaration/{index}',
                                   ['python3', 'scripts/run_declaration_linter.py', name],
                                   kind='check', check_kind='declaration', modules=[name], selection=[name])]]
    if selected_phases & {'provider-lint', 'consumers'}:
        for module in ('Aglib', 'AglibTest'):
            checks.append(full_lint(module + '/builtin', module, 'builtin'))
        for module in ('Aglib', 'AglibTest'):
            checks.append(full_lint(module + '/declaration', module, 'declaration'))
        all_lint = scope['providers'] + [n for n in scope['consumers'] + scope['tests']
                                       if n not in scope['facades']]
        other = [name for name in all_lint if not any(name == prefix or name.startswith(prefix + '.')
                 for prefix in ('Aglib', 'AglibTest'))]
        checks.extend(exact_lint('other', other))
        if scope['style']:
            checks.append(safe('all/style', ['python3', 'scripts/run_style_linter.py',
                               '--modules', *scope['style']], kind='check', check_kind='style',
                               modules=[], selection=scope['style'],
                               raw_paths=[str(module_path(name)) for name in scope['style']]))
    if 'trust' in selected_phases and scope['trust']:
        support = ['AglibTest.AuditSupport', 'AglibTest.AuditCoverage']
        if 'AglibTest/AuditSupport.lean' in scope['changed'] or scope.get('configuration_update'):
            checks.extend(exact_lint('audit-support', ['AglibTest.AuditSupport']))
        selected = sorted(set(n for n in scope['providers'] + scope['consumers'] + scope['tests']
                              if n not in scope['facades']))
        if 'AglibTest/AuditSupport.lean' in scope['changed'] or scope.get('configuration_update'):
            selected.append('AglibTest.AuditSupport')
        names = list(dict.fromkeys(['Aglib', 'AglibTest', *[name for name in selected
                    if not name.startswith(('Aglib.', 'AglibTest.'))]]))
        checks.append(safe('audit/all', audit_command(root, names), kind='check',
                           check_kind='audit', modules=sorted(set([*names, *support])), selection=names))
        if 'Audits/Aglib.lean' in scope['changed']:
            checks.extend([safe('legacy-audit-cached-imports', lake + ['--no-build', 'build', 'Aglib', *support]),
                           safe('legacy-audit-source', ['lake', 'env', 'lean', '-j1', 'Audits/Aglib.lean'])])
        if scope['controls']:
            controls = sorted(path.relative_to(root).as_posix()
                              for path in (root / 'AglibTest/NegativeControls').rglob('*.lean'))
            checks.append(safe('negative-controls', ['python3', 'scripts/check_negative_controls.py'],
                               kind='check', check_kind='controls', modules=support,
                               selection=support, raw_paths=controls))
        checks.append(safe('compiled-inventory', ['python3', 'scripts/check_compiled_inventory.py', '--modules',
                           *dict.fromkeys([*scope['providers'], *scope['consumers'], *scope['tests'], *support])]))
    clients = []
    if 'client' in selected_phases:
        before_client = []
        facades = {name.removeprefix('client:') for name in scope['facades'] if name.startswith('client:')}
        client_unrelated = sorted({name.removeprefix('client:') for target in set(scope['client']) & facades
                                  for name in scope['imports']['client:' + target]
                                  if name.removeprefix('client:') not in scope['client']})
        if client_unrelated:
            before_client.append(safe('client/cached-imports', lake + ['--no-build', 'build', *client_unrelated], client))
        client_checks = [safe('client-graph', lake + ['--no-build', 'build', 'Consumer'], client,
                              identity_modules=source_order(client, ['Consumer']))]
        if scope['client_audit']:
            client_checks.append(safe('client-audit', ['lake', 'env', 'lean', '-j1', 'Audit.lean'], client,
                                      kind='check', check_kind='client-audit', modules=['Consumer'],
                                      selection=['Consumer'], raw_paths=['Audit.lean']))
        group = {'id': 'client', 'cwd': str(client), 'before': before_client,
                 'build': False, 'checks': client_checks}
        if scope['client']:
            group['build_task'] = task('client/build', lake + ['build', *scope['client']], kind='build',
                                       cwd=client, modules=scope['client'])
        clients.append(group)
    if complete:
        clients.append({'id': 'root-export', 'build': False, 'checks': [
            safe('root-graph', lake + ['--no-build', 'build', 'Aglib', 'AglibTest',
                 '-o', directory / 'native-outputs.jsonl'], mapping=str(directory / 'native-outputs.jsonl'),
                 identity_modules=current_modules, export_order=0, export_label='root')]})
    return native_recipe(root, directory, source_checks=source_checks, prepare=prepare,
                         root_workspace={'id': 'root', 'before': before, 'build_task': graph,
                                         'checks': checks}, clients=clients, phase=phase)


def reflection_roots(root, task):
    roots = list(task['modules']) + ['Lean', 'Lake']
    if task['check_kind'] == 'declaration':
        roots += lean_imports((root / DRIVERS[0]).read_text())
    elif task['check_kind'] == 'audit':
        roots += lean_imports((root / AUDIT_DRIVER).read_text())
    elif task['check_kind'] == 'style':
        roots += lean_imports((root / DRIVERS[1]).read_text())
    elif task['check_kind'] == 'client-audit':
        roots += lean_imports((root / 'Audit.lean').read_text())
    elif task['check_kind'] == 'controls':
        roots += [name for path in task.get('raw_paths', ())
                  for name in lean_imports((root / path).read_text())
                  if not name.startswith('AglibTest.NegativeControls.')]
    return roots


def binding(root, task, toolchain, reflection=None, observations=None):
    if observations is not None:
        observations.assert_stable()
    arguments = task['command'][:]
    if task.get('generated'):
        arguments[-1] = '<selected-origin-audit>'
    client = task['check_kind'] == 'client-audit'
    owner = Path(task['cwd']) if client else root
    hash_file = observations.hash_file if observations else reflection.hash_file if reflection else file_hash
    policy = ['lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'] if client else POLICY + DRIVERS
    value = check_binding(owner, task['check_kind'], task['modules'], arguments,
                         policy, runtime_imports(root) if task['check_kind'] not in ('audit', 'client-audit') else (),
                         [*[str(module_path(n)) for n in task['modules']], *task.get('raw_paths', ())],
                         {k: v for k, v in toolchain.items() if k != 'installation'},
                         digest(task['generated']) if task.get('generated') else None, hash_file)
    if client:
        # The client's native graph/search path owns its Consumer environment.
        # Root checker policy remains bound under stable repository-relative names.
        optional = observations.optional_hash if observations else lambda path: file_hash(path) if path.is_file() else None
        value['repository_policy'] = {path: optional(root / path) for path in POLICY + DRIVERS}
        if reflection is not None and Path(reflection.root).resolve() != owner.resolve():
            reflection = None
    value['reflective_imports'] = reflection.closure(reflection_roots(owner, task)) if reflection else None
    if observations is not None:
        observations.assert_stable()
    return value


class AglibAdapter:
    """Aglib-owned scope, predicates and historical coverage; no transport policy."""
    def plan(self, root, repository, default_branch, head, requested_base=None, api=None):
        baseline = ci_baseline.select(root, repository, default_branch, head, requested_base, api)
        if GENERATED_MANIFEST in tree(root, head) and (root / GENERATED_MANIFEST).read_bytes() != manifest_bytes(root):
            raise ValueError('Tracked downstream manifest is stale; run python3 scripts/prepare_downstream.py '
                             'and commit it with the root dependency update before CI')
        scope = normalized_scope(root, affected_scope.select(root, baseline['base'], head=head,
                                                            allow_configuration_update=True))
        before = mathematical_tree(root, baseline['verified_base'])
        current = mathematical_tree(root, head)
        assert_native_scope(root, scope, before, current, scope['changed'])
        return {'baseline': baseline, 'scope': scope, 'baseline_math': before,
                'head_math': current, 'native_policy': native_policy(root, baseline, scope, before, current),
                'declaration_policy': declaration_policy(scope)}

    def required_phases(self, root, plan):
        return ['source', 'native'] if plan['scope']['native'] else ['source']

    def validate_plan(self, root, plan):
        expected_implementation = {Path(path).name: file_hash(root / path) for path in PACKAGE_SOURCES}
        if plan.get('implementation') != expected_implementation:
            raise ValueError('Executed lean_ci package differs from the committed Aglib implementation')
        scope, baseline = plan['scope'], plan['baseline']
        if (scope.get('working_tree') is not False or scope['head'] != plan['head']
                or scope['head'] != baseline['head'] or scope['base'] != baseline['base']):
            raise ValueError('CI plan is not bound to its verified committed source')
        if not ci_baseline.ancestor(root, baseline['base'], baseline['verified_base']):
            raise ValueError('Manual comparison advances beyond verified baseline')
        if not ci_baseline.ancestor(root, baseline['verified_base'], scope['head']):
            raise ValueError('Verified baseline is not an ancestor of current source')
        before = mathematical_tree(root, baseline['verified_base'])
        current = mathematical_tree(root, scope['head'])
        if before != plan['baseline_math'] or current != plan['head_math']:
            raise ValueError('Mathematical snapshot differs from CI plan')
        expected = normalized_scope(root, affected_scope.select(root, baseline['base'], head=scope['head'],
                                                               allow_configuration_update=True))
        if expected != scope:
            raise ValueError('Affected scope differs from authoritative committed selection')
        assert_native_scope(root, scope, before, current, scope['changed'])
        if plan.get('native_policy') != native_policy(root, baseline, scope, before, current):
            raise ValueError('Native semantic policy coverage differs from its explicit contract')
        if plan.get('declaration_policy') != declaration_policy(scope):
            raise ValueError('Declaration environment coverage differs from its explicit contract')

    tasks = staticmethod(tasks)
    binding = staticmethod(binding)

    def observe_inputs(self, root, observations):
        for path in POLICY:
            observations.optional_hash(root / path)

    def custom_task(self, root, plan, task, directory):
        if task['kind'] != 'links':
            raise ValueError('Unknown Aglib custom task: ' + task['kind'])
        check_links(root, plan['scope']['changed'])
        return {'checked': 'links'}

    def verify_custom_task(self, root, plan, task, result):
        if task['kind'] != 'links' or result != {'checked': 'links'}:
            raise ValueError('Missing source-link validation')
        check_links(root, plan['scope']['changed'])

    def summary(self, root, plan, records):
        scope = plan['scope']
        policy = {k: v for k, v in plan['native_policy'].items()
                  if k not in {'unchanged_production_origins', 'unchanged_test_origins'}}
        if 'origin_digest' in policy:
            policy['unchanged_production_origin_count'] = len(plan['native_policy']['unchanged_production_origins'])
            policy['unchanged_test_origin_count'] = len(plan['native_policy']['unchanged_test_origins'])
        return {'base': scope['base'],
                'coverage': 'complete-current-root-graph-and-selected-checks' if scope['native'] else 'inherited-unchanged-mathematical-snapshot',
                'check_reuse': 'per-check full native import closure; unsupported metadata reruns actual check',
                'native_check_policy': policy,
                'declaration_policy': plan['declaration_policy'],
                'build_identity': 'fresh Lake --rehash; refreshed trace observations are diagnostic, not a Python build key',
                'inherited_coverage': ([] if scope['native'] else ['unchanged mathematical source and pins'])
                    + ['unchanged origins retain the verified ancestor policy; no fresh per-leaf lint claim']
                    + (['unchanged-input rejection controls from verified baseline'] if not scope['controls'] else [])
                    + (['independent-client audit outside affected scope'] if scope['native'] and not scope['client_audit'] else []),
                'native_root_graph': scope['native'], 'client_graph': scope['native'],
                'selected_targets': scope['providers'] + scope['consumers'] + scope['tests'],
                'kernel_replay': 'not-requested; formal-acceptance evidence tracked externally'}


class AglibLocalAdapter(AglibAdapter):
    """Local selection over the same recipe, without committed-CI admission."""
    def __init__(self, selected=None, head=None, *, source_only=False, native_only=False, phases=None):
        self.selected, self.head = selected, head
        self.source_only, self.native_only = source_only, native_only
        self.phases = phases
        if source_only and native_only:
            raise ValueError('--source-only and --native-only are mutually exclusive')
        if phases and set(phases) - {'providers', 'provider-lint', 'consumers', 'trust', 'client'}:
            raise ValueError('Unknown local repair phase')

    def local_inputs(self, root, requested_base=None, targets=()):
        # Inventory names first; every source byte the selector can read is
        # observed before selection. Ignored native outputs are not source inputs.
        tracked = set(filter(None, git(root, 'ls-files', '-z').decode().split('\0')))
        paths = tracked | set(filter(None, git(root, 'ls-files', '--others',
                                              '--exclude-standard', '-z').decode().split('\0')))
        selected = {path for path in paths if path.endswith(('.lean', '.py'))
                    or path in POLICY or path in affected_scope.CONFIG}
        base = requested_base or (self.selected or {}).get('base')
        if base:
            selected.update(path for path in git(root, 'diff', '--name-only', '-z', '--no-renames',
                                                base).decode().split('\0') if path)
        selected.update(paths - tracked)
        selected.update(POLICY)
        selected.update(DRIVERS)
        selected.update(affected_scope.CONFIG)
        tracked_manifest = GENERATED_MANIFEST in tracked
        if not tracked_manifest:
            selected.discard(GENERATED_MANIFEST)
        directories = {'.'}
        for name in selected:
            if '.lake' in Path(name).parts:
                continue
            parent = Path(name).parent
            while parent != Path('.'):
                if (root / parent).is_dir():
                    directories.add(parent.as_posix())
                parent = parent.parent
        inputs = sorted(selected)
        for directory in sorted(directories):
            excluded = ['.git', '.lake', '__pycache__']
            if directory == 'examples/downstream' and not tracked_manifest:
                excluded.append('lake-manifest.json')
            inputs.append({'path': directory, 'exclude': excluded})
        return inputs

    def select_scope(self, root, requested_base=None, targets=(), source_basis=None):
        if targets:
            raise ValueError('Aglib local scope uses --base or an existing guarded --plan')
        if source_basis is None or source_basis['kind'] != 'working-tree':
            raise ValueError('Local final checks require an explicit working-tree source basis')
        if self.selected is not None:
            affected_scope.validate(root, self.selected)
            expected = (affected_scope.select(root, full=True) if self.selected['coverage'] == 'explicit-full' else
                        affected_scope.select(root, self.selected.get('base'),
                            None if self.selected['working_tree'] else self.selected['head']))
            if expected != self.selected:
                raise ValueError('Supplied scope differs from current source enrollment')
            scope = expected
        else:
            scope = affected_scope.select(root, requested_base, self.head)
        scope = normalized_scope(root, scope)
        if scope['native'] and not self.source_only:
            client = root / 'examples/downstream'
            if (not (client / '.lake').is_dir() or not (client / '.lake/packages').is_dir()
                    or not (client / 'lake-manifest.json').is_file()
                    or (client / 'lake-manifest.json').read_bytes() != manifest_bytes(root)):
                raise ValueError('Prepare matching dependencies and run python3 scripts/prepare_downstream.py '
                                 'before local final checks; prepared client setup must be idempotent')
        return {'scope': scope, 'declaration_policy': declaration_policy(scope)}

    def validate_local(self, root, plan):
        affected_scope.validate(root, plan['scope'])
        if plan['declaration_policy'] != declaration_policy(plan['scope']):
            raise ValueError('Local declaration environment policy changed')

    def tasks(self, root, plan, phase, directory):
        if phase != 'check':
            return tasks(root, plan, phase, directory)
        selected_phase = 'source' if self.source_only else 'native' if self.native_only else 'check'
        return tasks(root, plan, selected_phase, directory, phases=self.phases)

    def local_summary(self, root, plan, record):
        scope = plan['scope']
        native = scope['native'] and not self.source_only
        control = next((item for item in record['tasks'] if item['id'] == 'negative-controls'), None)
        controls = ('compatible-success-reused' if control and control['result'].get('mode') == 'reused' else
                    'executed' if control else
                    'unchanged-inputs; prior-compatible-coverage-required' if native and scope['trust'] and not scope['controls'] else
                    'not-selected')
        return {'coverage': scope['coverage'], 'base': scope['base'], 'head': scope['head'],
                'selected_targets': scope['providers'] + scope['consumers'] + scope['tests'],
                'declaration_policy': plan['declaration_policy'],
                'native_validation': 'performed-selected-groups' if native else 'not-performed',
                'source_validation': 'prior-compatible-coverage-required' if self.native_only else 'performed',
                'check_groups': (self.phases or ['providers', 'provider-lint', 'consumers', 'trust', 'client']) if native else [],
                'kernel_replay': 'not-requested; formal-acceptance evidence tracked externally',
                'negative_controls': controls}


def create_application(root):
    config = ResourceConfig(prefix='AGLIB', profile_keys=('R5_LEAN_REMOTE_PROFILE',))
    return Application(root, AglibLocalAdapter(), NativeRuntime(root, resource_config=config))


def create_plan(root, repository, default_branch, head, state, requested_base=None, api=None):
    return create_application(root).plan(repository, default_branch, head, state, requested_base, api)


def validate_plan(root, plan):
    return create_application(root).validate_plan(plan)


def run_phase(root, state, phase, progress=None, executor=None, toolchain=None):
    return create_application(root).run_phase(state, phase, progress, executor, toolchain)


def verify_phase(root, state, plan, phase, toolchain):
    return create_application(root).verify_phase(state, plan, phase, toolchain)


def finalize(root, state, outputs=None, toolchain=None):
    result = create_application(root).finalize(state, outputs, toolchain)
    print(json.dumps(result, indent=2))
    return result


def compiler_identity(root, hash_file=file_hash):
    return create_application(root).runtime.compiler_identity(hash_file)


def main(argv=None):
    return generic_main(argv, application=create_application(Path.cwd()))


if __name__ == '__main__':
    sys.exit(main())
