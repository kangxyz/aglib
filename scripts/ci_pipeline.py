#!/usr/bin/env python3
"""Plan, execute, and independently finalize committed incremental CI coverage."""
import argparse
from contextlib import contextmanager
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid

import affected_scope
import build_serial
import ci_baseline
from check_affected import check_links
from ci_state import (Progress, ReflectionGraph, ReflectionUnavailable, check_binding, digest, file_hash, read_json,
                      module_identity, valid_receipt, valid_success, write_json)
from library_sources import lean_imports, module_path
import resource_guard


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 1
POLICY = ['scripts/ci_pipeline.py', 'scripts/ci_state.py', 'scripts/resource_guard.py',
          'scripts/build_serial.py', 'scripts/library_sources.py',
          'scripts/run_declaration_linter.py', 'scripts/run_style_linter.py',
          'scripts/check_negative_controls.py', 'scripts/nolints.json', 'AglibTest/AuditSupport.lean',
          'AglibTest/AuditCoverage.lean', 'AglibTest/Axioms.lean',
          *sorted(affected_scope.CONFIG)]
DRIVERS = ['.lake/packages/batteries/scripts/runLinter.lean',
           '.lake/packages/mathlib/scripts/lint-style.lean']
GENERATED_MANIFEST = 'examples/downstream/lake-manifest.json'


def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root)


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
            if p.endswith('.lean') or p in affected_scope.CONFIG}


def source_files(root):
    result = {}
    for path, entry in tree(root, 'HEAD').items():
        target = root / path
        result[path] = (digest(os.readlink(target)) if entry['mode'] == '120000'
                        else file_hash(target))
    return result


def normalized_scope(root, scope):
    scope = json.loads(json.dumps(scope))
    # prepare_downstream owns this ignored, deterministic generated manifest.
    # Its input is the committed root manifest, never an independently trusted pin.
    if GENERATED_MANIFEST not in tree(root, 'HEAD'):
        scope['identity'].pop(GENERATED_MANIFEST, None)
    return scope


def assert_native_scope(root, scope, base_math, head_math, changed):
    """A second, source-based gate against accidentally empty/omitted math scope."""
    math_changed = {p for p in base_math.keys() | head_math.keys()
                    if base_math.get(p) != head_math.get(p)}
    controls_changed = bool(affected_scope.CONTROL_INPUTS.intersection(changed)
                            or any(p.startswith('AglibTest/NegativeControls/') for p in changed))
    if not scope['native'] and (math_changed or controls_changed or scope['controls']):
        raise ValueError('Changed mathematical/control inputs cannot have source-only native coverage')
    selected = set(scope['providers'] + scope['consumers'] + scope['tests'])
    for path in sorted(math_changed):
        if path in affected_scope.CONFIG:
            raise ValueError('Configuration/pin changes need an explicit validated migration scope: ' + path)
        if path.startswith('examples/downstream/'):
            if not scope['client_audit']:
                raise ValueError('Changed client mathematical input omitted from native audit scope: ' + path)
        elif path.startswith('AglibTest/NegativeControls/'):
            if not scope['controls'] or not scope['trust']:
                raise ValueError('Changed rejection control omitted from native scope: ' + path)
        elif path in {'AglibTest/Axioms.lean', 'AglibTest/AuditSupport.lean'}:
            if not scope['trust']:
                raise ValueError('Changed audit policy omitted from native scope: ' + path)
        elif path in head_math and affected_scope.node(path) not in selected:
            raise ValueError('Changed mathematical module omitted from native scope: ' + path)
    if controls_changed and not (scope['native'] and scope['trust'] and scope['controls']):
        raise ValueError('Changed control/runtime policy requires fresh native rejection controls')


def create_plan(root, repository, default_branch, head, state, requested_base=None, api=None):
    root, state = Path(root).resolve(), Path(state).resolve()
    if state.is_relative_to(root):
        raise ValueError('CI state must be outside the committed checkout')
    baseline = ci_baseline.select(root, repository, default_branch, head, requested_base, api)
    scope = normalized_scope(root, affected_scope.select(root, baseline['base'], head=head))
    before = mathematical_tree(root, baseline['verified_base'])
    current = mathematical_tree(root, head)
    assert_native_scope(root, scope, before, current, scope['changed'])
    plan = {'schema': SCHEMA, 'invocation': uuid.uuid4().hex, 'baseline': baseline,
            'scope': scope, 'source_files': source_files(root),
            'baseline_math': before, 'head_math': current,
            'required_phases': ['source', 'native'] if scope['native'] else ['source']}
    plan['id'] = digest(plan)
    state.mkdir(parents=True, exist_ok=True)
    if (state / 'plan.json').exists():
        raise ValueError('CI state already has a plan; use a fresh invocation directory')
    write_json(state / 'plan.json', plan)
    write_json(state / 'scope.json', scope)
    return plan


def validate_plan(root, plan):
    content = {key: value for key, value in plan.items() if key != 'id'}
    if plan.get('schema') != SCHEMA or plan.get('id') != digest(content):
        raise ValueError('Corrupt/wrong CI plan identity')
    scope, baseline = plan['scope'], plan['baseline']
    if (scope.get('working_tree') is not False or scope['head'] != baseline['head']
            or scope['base'] != baseline['base']):
        raise ValueError('CI plan is not bound to its verified committed source')
    if git(root, 'status', '--porcelain', '--untracked-files=all').strip():
        raise ValueError('CI committed source acquired working-tree changes')
    if git(root, 'rev-parse', 'HEAD').decode().strip() != scope['head']:
        raise ValueError('CI HEAD drifted')
    if source_files(root) != plan['source_files']:
        raise ValueError('CI source/configuration bytes drifted')
    if not ci_baseline.ancestor(root, baseline['base'], baseline['verified_base']):
        raise ValueError('Manual comparison advances beyond verified baseline')
    if not ci_baseline.ancestor(root, baseline['verified_base'], scope['head']):
        raise ValueError('Verified baseline is not an ancestor of current source')
    if (mathematical_tree(root, baseline['verified_base']) != plan['baseline_math']
            or mathematical_tree(root, scope['head']) != plan['head_math']):
        raise ValueError('Mathematical snapshot differs from CI plan')
    expected = normalized_scope(root, affected_scope.select(root, baseline['base'], head=scope['head']))
    if expected != scope:
        raise ValueError('Affected scope differs from authoritative committed selection')
    assert_native_scope(root, scope, plan['baseline_math'], plan['head_math'], scope['changed'])
    required = ['source', 'native'] if scope['native'] else ['source']
    if plan['required_phases'] != required:
        raise ValueError('Required CI phase set was altered')


def runtime_imports(root):
    imports = set()
    for path in DRIVERS:
        imports.update(n for n in lean_imports((root / path).read_text())
                       if n.startswith(('Batteries.', 'Mathlib.', 'Cli.', 'ImportGraph.')))
    return sorted(imports)


def audit_source(root, selected):
    legacy = (root / 'AglibTest/Axioms.lean').read_text()
    start = legacy.index('  let env ← getEnv\n')
    end = legacy.index('  logInfo m!"Audited ', start)
    return ('import AglibTest.AuditSupport\nimport AglibTest.AuditCoverage\n'
            + ''.join('import ' + n + '\n' for n in selected
                      if n not in {'AglibTest.AuditSupport', 'AglibTest.AuditCoverage'})
            + '\nopen Lean in\nrun_cmd do\n  let count ← AglibAudit.auditModules #['
            + ', '.join('`' + n for n in selected) + ']\n' + legacy[start:end]
            + '  logInfo m!"Selected-origin axiom audit: {count} declarations; '
              'private/generated origin control: {coverageCount}."\n')


def tasks(root, plan, phase, directory):
    """Reconstruct the required commands; phase records cannot waive any task."""
    scope, result = plan['scope'], []
    def add(name, args, kind='process', cwd=root, **extra):
        result.append({'id': name, 'kind': kind, 'command': list(map(str, args)),
                       'cwd': str(cwd), **extra})
    if phase == 'source':
        for script in ['generate_imports.py', 'check_library_layout.py',
                       'check_placeholders.py', 'check_source_policy.py']:
            add(script, ['python3', 'scripts/' + script] + (['--check'] if script == 'generate_imports.py' else []))
        add('links', [], kind='links')
        for test in scope['tooling_tests']:
            add('tooling/' + test, ['python3', '-m', 'unittest', 'discover', '-s',
                                  '.github/actions/lake-cache' if test == 'native-cache' else 'scripts',
                                  '-p', 'test_*.py' if test == 'native-cache' else test + '.py'])
        return result
    if phase != 'native' or not scope['native']:
        raise ValueError('Native phase was not required by this plan')
    lake = ['lake', '--rehash']
    def safe(name, args, cwd=root, **extra):
        add(name, args, cwd=cwd, capped=True, **extra)
    def build(name, names, cwd=root):
        if not names:
            return
        facades = {n.removeprefix('client:') for n in scope['facades']
                   if n.startswith('client:') == (cwd != root)}
        unrelated = set()
        for target in set(names) & facades:
            key = ('client:' if cwd != root else '') + target
            unrelated.update(n.removeprefix('client:') for n in scope['imports'][key]
                             if n.removeprefix('client:') not in names)
        if unrelated:
            safe(name + '/cached-imports', lake + ['--no-build', 'build', *sorted(unrelated)], cwd)
        add(name + '/build', lake + ['build', *names], kind='build', cwd=cwd, modules=names)
    all_lint = scope['providers'] + [n for n in scope['consumers'] + scope['tests'] if n not in scope['facades']]
    if 'AglibTest/AuditSupport.lean' in scope['changed']:
        all_lint.append('AglibTest.AuditSupport')
    imports = runtime_imports(root) if all_lint or scope['style'] else []
    graph_roots = list(dict.fromkeys(['Aglib', 'AglibTest',
                        *scope['providers'], *scope['consumers'], *scope['tests'],
                        *(['AglibTest.AuditSupport', 'AglibTest.AuditCoverage'] if scope['trust'] else [])]))
    current_modules = build_serial.source_order(root, graph_roots)
    selected = set(scope['providers'] + scope['consumers'] + scope['tests'])
    if scope['trust']:
        selected.update(['AglibTest.AuditSupport', 'AglibTest.AuditCoverage'])
    unrelated = sorted(set(current_modules) - selected)
    if unrelated:
        safe('unrelated-cached-imports', lake + ['--no-build', 'build', *unrelated])
    safe('shared-root-build', lake + ['build', *graph_roots, *('+' + n for n in imports)],
         kind='graph-build', modules=current_modules)
    add('reflection-environment', ['lake', 'env', 'printenv', 'LEAN_PATH'], kind='environment',
        environment_output=str(directory / 'import-search-path.txt'))
    # Consume traces from that successful shared graph. Lint does not repeatedly
    # rehash or query every module's transitive graph.
    lint_lake = ['lake', '--no-build']
    def lint(prefix, names, styles=()):
        for index, name in enumerate(names):
            for category, command in [('builtin', lint_lake + ['lint', '--builtin-only', name]),
                                      ('declaration', ['python3', 'scripts/run_declaration_linter.py', name])]:
                safe(f'{prefix}/{category}/{index}', command, kind='check',
                     check_kind=category, modules=[name], selection=[name])
        if styles:
            safe(prefix + '/style', ['python3', 'scripts/run_style_linter.py', '--modules', *styles])
    lint('providers', scope['providers'], scope['providers'])
    lint('consumers', [n for n in scope['consumers'] + scope['tests'] if n not in scope['facades']],
         sorted(set(scope['style']) - set(scope['providers'])))
    if scope['trust']:
        support = ['AglibTest.AuditSupport', 'AglibTest.AuditCoverage']
        if 'AglibTest/AuditSupport.lean' in scope['changed']:
            lint('audit-support', ['AglibTest.AuditSupport'])
        selected = sorted(set(n for n in scope['providers'] + scope['consumers'] + scope['tests']
                              if n not in scope['facades']))
        if 'AglibTest/AuditSupport.lean' in scope['changed']:
            selected.append('AglibTest.AuditSupport')
        for index, name in enumerate(selected or ['AglibTest.AuditCoverage']):
            audit = directory / f'SelectedAudit-{index:04d}.lean'
            safe(f'audit/{index}', ['lake', 'env', 'lean', '-j1', audit], kind='check',
                 check_kind='audit', modules=sorted(set([name, *support])), selection=[name],
                 generated=audit_source(root, [name]))
        if 'AglibTest/Axioms.lean' in scope['changed']:
            safe('legacy-audit-cached-imports', lake + ['--no-build', 'build', 'Aglib', *support])
            safe('legacy-audit-source', ['lake', 'env', 'lean', '-j1', 'AglibTest/Axioms.lean'])
        if scope['controls']:
            safe('negative-controls', ['python3', 'scripts/check_negative_controls.py'])
        safe('compiled-inventory', ['python3', 'scripts/check_compiled_inventory.py', '--modules',
                                   *dict.fromkeys([*scope['providers'], *scope['consumers'], *scope['tests'], *support])])
    client = root / 'examples/downstream'
    add('prepare-client', ['python3', 'scripts/prepare_downstream.py'])
    build('client', scope['client'], client)
    safe('client-graph', lake + ['--no-build', 'build', 'Consumer'], client,
         identity_modules=build_serial.source_order(client, ['Consumer']))
    if scope['client_audit']:
        safe('client-audit', ['lake', 'env', 'lean', '-j1', 'Audit.lean'], client)
    # This final barrier never turns a cold unrelated forest into compilation.
    safe('root-graph', lake + ['--no-build', 'build', 'Aglib', 'AglibTest',
                              '-o', directory / 'native-outputs.jsonl'],
         mapping=str(directory / 'native-outputs.jsonl'), identity_modules=current_modules)
    return result


def compiler_identity(root):
    result = {}
    for tool in ('lean', 'lake'):
        path = Path(subprocess.check_output(['elan', 'which', tool], cwd=root, text=True).strip())
        result[tool] = file_hash(path)
        if tool == 'lean':
            result['installation'] = str(path.resolve().parent.parent)
            library = path.parent.parent / 'lib/lean'
            for pattern in ('libleanshared*', 'libLake_shared*'):
                for shared in sorted(library.glob(pattern)):
                    if shared.is_file():
                        result[shared.name] = file_hash(shared)
    return result


def reflection_roots(root, task):
    roots = list(task['modules']) + ['Lean', 'Lake']
    if task['check_kind'] == 'declaration':
        roots += lean_imports((root / DRIVERS[0]).read_text())
    return roots


def binding(root, task, toolchain, reflection=None):
    arguments = task['command'][:]
    if task.get('generated'):
        arguments[-1] = '<selected-origin-audit>'
    value = check_binding(root, task['check_kind'], task['modules'], arguments,
                         POLICY + DRIVERS, runtime_imports(root) if task['check_kind'] != 'audit' else (),
                         [str(module_path(n)) for n in task['modules']],
                         {k: v for k, v in toolchain.items() if k != 'installation'},
                         digest(task['generated']) if task.get('generated') else None,
                         reflection.hash_file if reflection else file_hash)
    value['reflective_imports'] = reflection.closure(reflection_roots(root, task)) if reflection else None
    return value


def command_matches(logical, actual):
    logical, actual = list(logical), list(actual)
    if logical[:3] == ['lake', 'env', 'lean'] and len(actual) == len(logical):
        if Path(actual[2]).name != 'lean':
            return False
        actual[2] = 'lean'
    return actual == logical


class Executor:
    def __init__(self, root):
        self.root = root

    def run(self, task, directory):
        directory.mkdir(parents=True, exist_ok=True)
        cwd, command = Path(task['cwd']), task['command']
        generated_stamp = None
        if task.get('generated'):
            Path(command[-1]).write_text(task['generated'])
            generated_stamp = ReflectionGraph.stamp(Path(command[-1]))
        if task['kind'] == 'build':
            before = {n: self.trace_stamp(cwd, n) for n in task['modules']}
            code = build_serial.build(cwd, task['modules'], directory, rehash=True)
            if code:
                raise ValueError(f'Selected build failed ({code}): {task["id"]}')
            cached = read_json(directory / 'cached-check.json')
            if valid_receipt(cached, ['lake', '--rehash', '--no-build', 'build', *task['modules']], cwd):
                receipt, performed = cached, False
            else:
                if (cached.get('exit_code') != 3 or cached.get('guard_failure', 'missing') is not None
                        or cached.get('owned_group_gone') is not True
                        or not build_serial.expected_cache_miss(3, (directory / 'cached-check.log').read_text())):
                    raise ValueError('Selected build has no valid cache-miss evidence')
                receipt, performed = read_json(directory / 'graph-build.json'), True
                if not valid_receipt(receipt, command, cwd):
                    raise ValueError('Selected build has no successful guarded native graph receipt')
            compiled = [n for n in task['modules'] if performed and self.trace_stamp(cwd, n) != before[n]]
            return {'receipt': receipt, 'compiled_or_refreshed': compiled,
                    'reused_build_targets': [] if performed else task['modules']}
        before = {n: self.trace_stamp(cwd, n) for n in task.get('modules', [])}
        budget = resource_guard.limits()
        receipt_path = directory / 'resource.json'
        if task['kind'] == 'environment':
            with Path(task['environment_output']).open('w') as output:
                code = resource_guard.run(command, cwd=cwd, receipt=receipt_path, budget=budget, stdout=output)
        elif task.get('capped'):
            threads = build_serial.build_threads()
            budget['native_build_threads'] = threads
            with build_serial.capped_toolchain(cwd, threads=threads) as env:
                bounded = resource_guard.capped_command(command, env)
                code = resource_guard.run(bounded, cwd=cwd, env=env, receipt=receipt_path, budget=budget)
        else:
            code = resource_guard.run(command, cwd=cwd, receipt=receipt_path, budget=budget)
        receipt = read_json(receipt_path)
        if task.get('generated') and (Path(command[-1]).read_text() != task['generated']
                                     or ReflectionGraph.stamp(Path(command[-1])) != generated_stamp):
            raise ValueError('Generated audit input drifted during execution')
        if code or not valid_receipt(receipt, cwd=cwd) or not command_matches(command, receipt['command']):
            diagnostic = '; recover matching caches for the missing scope; no cold-build fallback' if task['id'].endswith(('cached-imports', 'graph')) else ''
            raise ValueError(f'CI task failed: {task["id"]}{diagnostic}')
        result = {'receipt': receipt}
        if task['kind'] == 'environment':
            result['search_path'] = parse_search_path(Path(task['environment_output']).read_text())
            result['output_sha256'] = file_hash(task['environment_output'])
        if task['kind'] == 'graph-build':
            result['compiled_or_refreshed'] = [n for n in task['modules'] if self.trace_stamp(cwd, n) != before[n]]
            result['reused_build_targets'] = [n for n in task['modules'] if self.trace_stamp(cwd, n) == before[n]]
        if task.get('mapping'):
            path = Path(task['mapping'])
            if not path.is_file() or not path.stat().st_size:
                raise ValueError('Successful root graph did not produce native Lake mappings')
            result['mapping_sha256'] = file_hash(path)
        if task.get('identity_modules'):
            result['native_modules'] = {n: module_identity(cwd, n, getattr(self, 'artifact_hasher', file_hash))
                                        for n in task['identity_modules']}
        return result

    @staticmethod
    def trace_stamp(root, name):
        path = root / '.lake/build/lib/lean' / module_path(name).with_suffix('.trace')
        return (path.stat().st_mtime_ns, file_hash(path)) if path.is_file() else None


@contextmanager
def locked(state):
    path = state / '.lock'
    descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    try:
        os.close(descriptor)
        yield
    finally:
        path.unlink()


def parse_search_path(output):
    paths = output.strip().split(os.pathsep) if output.strip() else []
    if any(not Path(p).is_absolute() for p in paths):
        raise ValueError('Unknown/nonabsolute resolved Lake import search path')
    return paths


def make_reflection(root, result, toolchain):
    try:
        return ReflectionGraph(root, result['search_path'], toolchain)
    except ReflectionUnavailable:
        return None


def verify_task(root, task, result, toolchain, reflection=None):
    if not isinstance(result, dict):
        raise ValueError('Missing structured command evidence: ' + task['id'])
    if task['kind'] == 'links':
        if result != {'checked': 'links'}:
            raise ValueError('Missing source-link validation')
        return
    if task['kind'] == 'check':
        current_binding = binding(root, task, toolchain, reflection)
        if (result.get('mode') not in ('performed', 'reused')
                or not valid_success(result.get('success'), current_binding)
                or (result['mode'] == 'reused' and current_binding['reflective_imports'] is None)):
            raise ValueError('Missing/stale/corrupt individual check success: ' + task['id'])
        if not command_matches(task['command'], result['success']['receipt']['command']):
            # A reused selected audit used the same generated text at an older path.
            actual = result['success']['receipt']['command'][:]
            logical = task['command'][:]
            if task.get('generated'):
                actual[-1] = logical[-1]
            if not command_matches(logical, actual):
                raise ValueError('Check receipt command differs from required command')
        return
    receipt = result.get('receipt')
    if not valid_receipt(receipt, cwd=task['cwd']):
        raise ValueError('Missing successful resource receipt: ' + task['id'])
    expected = task['command']
    if task['kind'] == 'build' and receipt['command'] == expected[:2] + ['--no-build'] + expected[2:]:
        pass
    elif not command_matches(expected, receipt['command']):
        raise ValueError('Wrong native/source command receipt: ' + task['id'])
    if task.get('mapping') and (not Path(task['mapping']).is_file()
                               or result.get('mapping_sha256') != file_hash(task['mapping'])):
        raise ValueError('Missing/corrupt complete native mappings')
    if task.get('identity_modules') and result.get('native_modules') != {
            n: module_identity(Path(task['cwd']), n, reflection.hash_file if reflection else file_hash)
            for n in task['identity_modules']}:
        raise ValueError('Current complete native graph outputs drifted: ' + task['id'])
    if task['kind'] == 'environment':
        path = Path(task['environment_output'])
        if result.get('output_sha256') != file_hash(path) or result.get('search_path') != parse_search_path(path.read_text()):
            raise ValueError('Wrong/missing actual native import search-path evidence')


def run_phase(root, state, phase, progress=None, executor=None, toolchain=None):
    root, state = Path(root).resolve(), Path(state).resolve()
    if state.is_relative_to(root):
        raise ValueError('CI state must be outside the committed checkout')
    with locked(state):
        (state / 'complete.json').unlink(missing_ok=True)
        plan = read_json(state / 'plan.json')
        validate_plan(root, plan)
        source_stamps = {p: ReflectionGraph.stamp(root / p) for p in plan['source_files']}
        if phase not in plan['required_phases']:
            raise ValueError('Phase is not required by authoritative CI plan: ' + phase)
        if phase == 'native':
            verify_phase(root, state, plan, 'source', None)
        directory = state / 'runs' / (phase + '-' + uuid.uuid4().hex)
        directory.mkdir(parents=True)
        record = {'schema': SCHEMA, 'plan_id': plan['id'], 'phase': phase,
                  'directory': str(directory), 'status': 'running', 'tasks': []}
        write_json(state / (phase + '.json'), record)
        required = tasks(root, plan, phase, directory)
        executor = executor or Executor(root)
        progress = Progress(progress or state / 'check-progress')
        observe_toolchain = toolchain is None and phase == 'native'
        toolchain = toolchain or (compiler_identity(root) if phase == 'native' else None)
        reflection = None
        for index, task in enumerate(required):
            if task['kind'] == 'links':
                check_links(root, plan['scope']['changed'])
                result = {'checked': 'links'}
            elif task['kind'] == 'check':
                def execute(task=task, index=index):
                    evidence = executor.run(task, directory / f'task-{index:04d}')
                    return evidence['receipt'], evidence['receipt']['command']
                current = binding(root, task, toolchain, reflection)
                result = progress.run(lambda task=task: binding(root, task, toolchain, reflection), execute,
                                      reuse=current['reflective_imports'] is not None)
            else:
                result = executor.run(task, directory / f'task-{index:04d}')
            verify_task(root, task, result, toolchain, reflection)
            if task['kind'] == 'environment':
                reflection = make_reflection(root, result, toolchain)
                if reflection is not None:
                    executor.artifact_hasher = reflection.hash_file
            record['tasks'].append({'id': task['id'], 'specification': digest(task), 'result': result})
            write_json(state / (phase + '.json'), record)
        validate_plan(root, plan)
        if any(ReflectionGraph.stamp(root / p) != stamp for p, stamp in source_stamps.items()):
            raise ValueError('Committed source changed and/or was restored during phase execution')
        if reflection is not None:
            reflection.assert_stable()
        if observe_toolchain and compiler_identity(root) != toolchain:
            raise ValueError('Native toolchain changed during phase execution')
        record['status'] = 'completed'
        record['toolchain'] = toolchain
        write_json(state / (phase + '.json'), record)
        return record


def verify_phase(root, state, plan, phase, toolchain):
    record = read_json(state / (phase + '.json'))
    if (not isinstance(record, dict) or record.get('schema') != SCHEMA or record.get('plan_id') != plan['id']
            or record.get('phase') != phase or record.get('status') != 'completed'):
        raise ValueError('Missing/incomplete/wrong-plan required CI phase: ' + phase)
    if not isinstance(record.get('directory'), str):
        raise ValueError('Missing required phase execution evidence: ' + phase)
    directory = Path(record['directory'])
    if not directory.is_relative_to(state / 'runs'):
        raise ValueError('Phase evidence escaped its invocation')
    required = tasks(root, plan, phase, directory)
    actual = record.get('tasks')
    if not isinstance(actual, list) or len(actual) != len(required):
        raise ValueError('Required phase task coverage is incomplete: ' + phase)
    if phase == 'native' and record.get('toolchain') != toolchain:
        raise ValueError('Native toolchain changed since execution')
    reflection = None
    for task, item in zip(required, actual):
        if not isinstance(item, dict) or item.get('id') != task['id'] or item.get('specification') != digest(task):
            raise ValueError('Wrong/forged phase task specification: ' + task['id'])
        verify_task(root, task, item.get('result'), toolchain, reflection)
        if task['kind'] == 'environment':
            reflection = make_reflection(root, item['result'], toolchain)
    if reflection is not None:
        reflection.assert_stable()
    if phase == 'source':
        check_links(root, plan['scope']['changed'])
    return record


def finalize(root, state, outputs=None, toolchain=None):
    root, state = Path(root).resolve(), Path(state).resolve()
    if state.is_relative_to(root) or (outputs and Path(outputs).resolve().is_relative_to(root)):
        raise ValueError('CI state and coverage outputs must be outside the committed checkout')
    with locked(state):
        (state / 'complete.json').unlink(missing_ok=True)
        if outputs:
            outputs = Path(outputs)
            outputs.unlink(missing_ok=True)
            outputs.with_suffix(outputs.suffix + '.coverage.json').unlink(missing_ok=True)
        plan = read_json(state / 'plan.json')
        validate_plan(root, plan)
        scope, baseline = plan['scope'], plan['baseline']
        toolchain = toolchain or (compiler_identity(root) if scope['native'] else None)
        records = [verify_phase(root, state, plan, phase, toolchain)
                   for phase in plan['required_phases']]
        validate_plan(root, plan)
        outcomes = [item for record in records for item in record['tasks']]
        checks = [item for item in outcomes if 'mode' in item['result']]
        compiled = [n for item in outcomes for n in item['result'].get('compiled_or_refreshed', [])]
        reused = [n for item in outcomes for n in item['result'].get('reused_build_targets', [])]
        summary = {'schema': SCHEMA, 'status': 'complete', 'plan_id': plan['id'],
                   'base': scope['base'], 'head': scope['head'], 'baseline': baseline,
                   'coverage': 'complete-current-root-graph-and-selected-checks' if scope['native'] else 'inherited-unchanged-mathematical-snapshot',
                   'required_phases': plan['required_phases'], 'performed_phases': [r['phase'] for r in records],
                   'performed_checks': [i['id'] for i in checks if i['result']['mode'] == 'performed'],
                   'reused_checks': [i['id'] for i in checks if i['result']['mode'] == 'reused'],
                   'check_reuse': 'per-check full native import closure; unsupported metadata reruns actual check',
                   'compiled_or_refreshed_targets': sorted(set(compiled)),
                   'reused_build_targets': sorted(set(reused)),
                   'build_identity': 'fresh Lake --rehash; refreshed trace observations are diagnostic, not a Python build key',
                   'inherited_coverage': ([] if scope['native'] else ['unchanged mathematical source and pins'])
                       + (['unchanged-input rejection controls from verified baseline'] if not scope['controls'] else [])
                       + (['independent-client audit outside affected scope'] if scope['native'] and not scope['client_audit'] else []),
                   'native_root_graph': scope['native'], 'client_graph': scope['native'],
                   'selected_targets': scope['providers'] + scope['consumers'] + scope['tests'],
                   'kernel_replay': 'not-requested; formal-acceptance evidence tracked externally'}
        if outputs and scope['native']:
            native_record = next(r for r in records if r['phase'] == 'native')
            mapping = Path(native_record['directory']) / 'native-outputs.jsonl'
            outputs = Path(outputs)
            outputs.parent.mkdir(parents=True, exist_ok=True)
            outputs.write_bytes(mapping.read_bytes())
            write_json(outputs.with_suffix(outputs.suffix + '.coverage.json'), summary)
        write_json(state / 'complete.json', summary)
        print(json.dumps(summary, indent=2))
        return summary


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['plan', 'source', 'native', 'finalize'])
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--repository')
    parser.add_argument('--default-branch', default='main')
    parser.add_argument('--head')
    parser.add_argument('--requested-base')
    parser.add_argument('--github-output', type=Path)
    parser.add_argument('--progress', type=Path)
    parser.add_argument('--outputs', type=Path)
    args = parser.parse_args(argv)
    root = Path.cwd()
    try:
        if args.phase == 'plan':
            if not args.repository or not args.head:
                raise ValueError('Planning requires --repository and exact --head')
            plan = create_plan(root, args.repository, args.default_branch, args.head,
                               args.state, args.requested_base)
            if args.github_output:
                with args.github_output.open('a') as output:
                    for key in ('native', 'publish'):
                        output.write(key + '=' + str(plan['scope'][key]).lower() + '\n')
            print(f"CI plan {plan['id']}: base={plan['scope']['base']} head={plan['scope']['head']} "
                  f"native={plan['scope']['native']} baseline run={plan['baseline']['run_id']}")
        elif args.phase == 'finalize':
            finalize(root, args.state, args.outputs)
        else:
            run_phase(root, args.state, args.phase, args.progress)
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print('CI core failed closed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
