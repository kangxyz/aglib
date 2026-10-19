"""Repository-independent CI lifecycle with strict, reconstructed coverage.

Adapters are trusted committed policy. They choose coverage and check inputs;
this module alone admits receipts, phase completion and publication. Progress
records are compatibility evidence from a trusted producer, not signatures.
"""
from contextlib import contextmanager
import json
import os
from pathlib import Path
import shutil
import subprocess
import uuid

from .runtime import NativeRuntime, command_matches, parse_search_path
from .state import (Progress, ReflectionGraph, ReflectionUnavailable, TemporalInputs,
                    digest, file_hash, module_identity, read_json, valid_receipt,
                    valid_success, write_json)

SCHEMA = 1
PLAN_FIELDS = {'schema', 'id', 'invocation', 'head', 'repository', 'source_files', 'required_phases', 'implementation'}
SUMMARY_FIELDS = {'implementation', 'schema', 'status', 'plan_id', 'head', 'baseline', 'required_phases',
                  'performed_phases', 'performed_checks', 'reused_checks',
                  'compiled_or_refreshed_targets', 'reused_build_targets'}
STANDARD_KINDS = {'process', 'build', 'graph-build', 'environment', 'check'}


IMPLEMENTATION_OWNERS = ('__init__.py', '__main__.py', 'build.py', 'cli.py', 'engine.py',
                         'github.py', 'resources.py', 'runtime.py', 'source.py', 'state.py')


def implementation_sources():
    """Actual installed package owners, independent of any repository copy."""
    directory = Path(__file__).absolute().parent
    return {name: directory / name for name in IMPLEMENTATION_OWNERS}


def implementation_identity(observations=None):
    """Content-only identity; paths and temporal stamps never enter reuse keys."""
    hash_file = observations.hash_file if observations is not None else file_hash
    return {name: hash_file(path) for name, path in sorted(implementation_sources().items())}


def git(root, *arguments):
    return subprocess.check_output(['git', *arguments], cwd=root)


def source_files(root):
    """All tracked bytes, including symlink values, at the actual committed HEAD."""
    result = {}
    for row in git(root, 'ls-tree', '-rz', '--full-tree', 'HEAD').split(b'\0'):
        if not row:
            continue
        metadata, raw_path = row.split(b'\t', 1)
        mode, kind, _ = metadata.decode().split()
        path = os.fsdecode(raw_path)
        if kind != 'blob' or mode not in {'100644', '100755', '120000'}:
            raise ValueError('Unsupported committed source entry: ' + path)
        result[path] = digest(os.readlink(root / path)) if mode == '120000' else file_hash(root / path)
    return result


@contextmanager
def locked(state):
    descriptor = os.open(state / '.lock', os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    try:
        os.close(descriptor)
        yield
    finally:
        (state / '.lock').unlink()


class Application:
    """Small policy interface: plan, required_phases, validate_plan, tasks, binding.

    Optional hooks: custom_task/verify_custom_task, observe_inputs, summary.
    Tasks setting establishes_inputs=True trigger observe_inputs after setup.
    binding must return the state's standard check-binding schema, including
    arguments and reflective_imports. Unsupported reflection disables reuse.
    """
    def __init__(self, root, adapter, runtime=None):
        self.root = Path(root).resolve()
        self.adapter = adapter
        self.runtime = runtime or NativeRuntime(self.root)

    def _external(self, path):
        path = Path(path).resolve()
        if path.is_relative_to(self.root):
            raise ValueError('CI state, progress and coverage outputs must be outside the committed checkout')
        return path

    def _clean_head(self, head):
        if git(self.root, 'status', '--porcelain', '--untracked-files=all').strip():
            raise ValueError('CI committed source has working-tree changes')
        if git(self.root, 'rev-parse', 'HEAD').decode().strip() != head:
            raise ValueError('CI HEAD drifted')

    def _phases(self, payload):
        phases = self.adapter.required_phases(self.root, payload)
        if phases not in (['source'], ['source', 'native']):
            raise ValueError('Required phases must be source, optionally followed by native')
        return list(phases)

    def _source_observer(self, plan):
        observations = TemporalInputs()
        for path in plan['source_files']:
            observations.observe_resolution(self.root / path)
        if implementation_identity(observations) != plan['implementation']:
            raise ValueError('CI implementation bytes differ from planned implementation')
        observations.assert_stable()
        return observations

    def plan(self, repository, default_branch, head, state, requested_base=None, api=None):
        state = self._external(state)
        self._clean_head(head)
        initial = source_files(self.root)
        implementation = implementation_identity()
        observer = self._source_observer({'source_files': initial, 'implementation': implementation})
        payload = self.adapter.plan(self.root, repository, default_branch, head,
                                    requested_base=requested_base, api=api)
        if not isinstance(payload, dict) or PLAN_FIELDS.intersection(payload):
            raise ValueError('Adapter plan attempted to override core envelope fields')
        plan = dict(payload, schema=SCHEMA, invocation=uuid.uuid4().hex, head=head, repository=repository,
                    source_files=initial, required_phases=self._phases(payload), implementation=implementation)
        plan['id'] = digest(plan)
        self.validate_plan(plan)
        observer.assert_stable()
        state.mkdir(parents=True, exist_ok=True)
        with locked(state):
            if (state / 'plan.json').exists():
                raise ValueError('CI state already has a plan; use a fresh invocation directory')
            write_json(state / 'plan.json', plan)
            if 'scope' in plan:
                write_json(state / 'scope.json', plan['scope'])
        return plan

    def validate_plan(self, plan):
        if (not isinstance(plan, dict) or plan.get('schema') != SCHEMA
                or not isinstance(plan.get('invocation'), str) or not plan['invocation']
                or plan.get('id') != digest({k: v for k, v in plan.items() if k != 'id'})):
            raise ValueError('Corrupt/wrong CI plan identity')
        if plan.get('implementation') != implementation_identity():
            raise ValueError('CI implementation bytes differ from planned implementation')
        self._clean_head(plan['head'])
        if source_files(self.root) != plan.get('source_files'):
            raise ValueError('CI source/configuration bytes drifted')
        if plan.get('required_phases') != self._phases(plan):
            raise ValueError('Required CI phase set was altered')
        self.adapter.validate_plan(self.root, plan)

    def _tasks(self, plan, phase, directory):
        tasks = self.adapter.tasks(self.root, plan, phase, directory)
        if not isinstance(tasks, list) or not tasks:
            raise ValueError('Required phase must specify actual validation tasks: ' + phase)
        identifiers = set()
        for task in tasks:
            if (not isinstance(task, dict) or not isinstance(task.get('id'), str) or not task['id']
                    or task['id'] in identifiers or not isinstance(task.get('kind'), str)
                    or not isinstance(task.get('command'), list)
                    or any(not isinstance(arg, str) for arg in task['command'])
                    or not isinstance(task.get('cwd'), str) or not Path(task['cwd']).is_absolute()):
                raise ValueError('Malformed/duplicate required task')
            if task['kind'] in STANDARD_KINDS and not task['command']:
                raise ValueError('Standard task requires a direct command: ' + task['id'])
            if task['kind'] == 'check' and phase != 'native':
                raise ValueError('Individual native checks require the native phase')
            identifiers.add(task['id'])
        return tasks

    def _observe_inputs(self, task, observations):
        if task.get('establishes_inputs'):
            hook = getattr(self.adapter, 'observe_inputs', None)
            if hook:
                hook(self.root, observations)
            observations.assert_stable()

    def _binding(self, plan, task, toolchain, reflection, observations):
        observations.assert_stable()
        cwd = Path(task['cwd']).resolve()
        if not cwd.is_relative_to(self.root):
            raise ValueError('Check working directory must be inside its repository')
        semantic_toolchain = {key: value for key, value in (toolchain or {}).items() if key != 'installation'}
        value = self.adapter.binding(self.root, task, semantic_toolchain, reflection=reflection,
                                     observations=observations)
        if not isinstance(value, dict) or not isinstance(value.get('arguments'), list):
            raise ValueError('Adapter omitted required check binding')
        # Bind the execution mechanics independently of repository policy fields.
        value = dict(value)
        value['execution'] = {'cwd': cwd.relative_to(self.root).as_posix(),
                              'repository': plan['repository'], 'implementation': plan['implementation'],
                              'kind': task['kind'],
                              'capped': bool(task.get('capped')),
                              'toolchain': semantic_toolchain,
                              'generated': digest(task['generated']) if task.get('generated') else None}
        observations.assert_stable()
        return value

    def _reflection(self, result, toolchain, observations):
        try:
            return ReflectionGraph(self.root, result['search_path'], toolchain, observations=observations)
        except ReflectionUnavailable:
            return None

    def _task_toolchain(self, task, expected, observations):
        actual = self.runtime.compiler_identity(observations.hash_file, cwd=task['cwd'])
        if actual != expected:
            raise ValueError('Mixed native compiler/runtime identities are unsupported: ' + task['cwd'])
        observations.assert_stable()

    def verify_task(self, plan, task, result, toolchain, reflection, observations):
        if not isinstance(result, dict):
            raise ValueError('Missing structured command evidence: ' + task['id'])
        kind = task['kind']
        if kind not in STANDARD_KINDS:
            # A custom validator cannot waive the standard-kind receipt checks.
            validator = getattr(self.adapter, 'verify_custom_task', None)
            if validator is None:
                raise ValueError('No validator for custom task: ' + kind)
            validator(self.root, plan, task, result)
            return
        if kind == 'check':
            current = self._binding(plan, task, toolchain, reflection, observations)
            if (result.get('mode') not in ('performed', 'reused')
                    or not valid_success(result.get('success'), current)
                    or (result['mode'] == 'reused' and current.get('reflective_imports') is None)):
                raise ValueError('Missing/stale/corrupt individual check success: ' + task['id'])
            receipt = result['success']['receipt']
            if (not isinstance(receipt.get('cwd'), str) or not Path(receipt['cwd']).is_absolute()
                    or (result['mode'] == 'performed' and not valid_receipt(receipt, cwd=task['cwd']))):
                raise ValueError('Wrong check receipt working directory: ' + task['id'])
            actual, expected = list(receipt['command']), list(task['command'])
            if task.get('generated') and result['mode'] == 'reused':
                actual[-1] = expected[-1]
            if not command_matches(expected, actual):
                raise ValueError('Check receipt command differs from required command')
            return
        receipt = result.get('receipt')
        if not valid_receipt(receipt, cwd=task['cwd']):
            raise ValueError('Missing successful resource receipt: ' + task['id'])
        expected = task['command']
        cached = kind == 'build' and receipt['command'] == expected[:2] + ['--no-build'] + expected[2:]
        if not cached and not command_matches(expected, receipt['command']):
            raise ValueError('Wrong native/source command receipt: ' + task['id'])
        if task.get('mapping'):
            path = Path(task['mapping'])
            if (not path.is_file() or not path.stat().st_size
                    or result.get('mapping_sha256') != observations.hash_file(path)):
                raise ValueError('Missing/corrupt complete native mappings')
        if task.get('identity_modules') and result.get('native_modules') != {
                name: module_identity(Path(task['cwd']), name, observations.hash_file)
                for name in task['identity_modules']}:
            raise ValueError('Current complete native graph outputs drifted: ' + task['id'])
        if kind == 'environment':
            path = Path(task['environment_output'])
            if (result.get('output_sha256') != observations.hash_file(path)
                    or result.get('search_path') != parse_search_path(path.read_text())):
                raise ValueError('Wrong/missing actual native import search-path evidence')

    def run_phase(self, state, phase, progress=None, executor=None, toolchain=None):
        state = self._external(state)
        progress = self._external(progress or state / 'check-progress')
        with locked(state):
            (state / 'complete.json').unlink(missing_ok=True)
            plan = read_json(state / 'plan.json')
            self.validate_plan(plan)
            observations = self._source_observer(plan)
            if phase not in plan['required_phases']:
                raise ValueError('Phase is not required by authoritative CI plan: ' + phase)
            if phase == 'native':
                self.verify_phase(state, plan, 'source', None)
            directory = state / 'runs' / (phase + '-' + uuid.uuid4().hex)
            directory.mkdir(parents=True)
            record = {'schema': SCHEMA, 'plan_id': plan['id'], 'phase': phase,
                      'directory': str(directory), 'status': 'running', 'tasks': []}
            write_json(state / (phase + '.json'), record)
            required = self._tasks(plan, phase, directory)
            executor = executor or self.runtime
            progress_store = Progress(progress)
            observe_toolchain = toolchain is None and phase == 'native'
            if observe_toolchain:
                toolchain = self.runtime.compiler_identity(observations.hash_file)
            reflection = None
            for index, task in enumerate(required):
                task_directory = directory / f'task-{index:04d}'
                kind = task['kind']
                if observe_toolchain:
                    self._task_toolchain(task, toolchain, observations)
                if kind not in STANDARD_KINDS:
                    handler = getattr(self.adapter, 'custom_task', None)
                    if handler is None:
                        raise ValueError('No custom task executor: ' + kind)
                    result = handler(self.root, plan, task, task_directory)
                elif kind == 'check':
                    def execute(task=task, task_directory=task_directory):
                        evidence = executor.run(task, task_directory)
                        if observe_toolchain:
                            self._task_toolchain(task, toolchain, observations)
                        if (not isinstance(evidence, dict)
                                or not valid_receipt(evidence.get('receipt'), cwd=task['cwd'])
                                or not command_matches(task['command'], evidence['receipt']['command'])):
                            raise ValueError('Check command omitted its actual validated receipt')
                        observations.assert_stable()
                        return evidence['receipt'], evidence['receipt']['command']
                    current = self._binding(plan, task, toolchain, reflection, observations)
                    result = progress_store.run(
                        lambda task=task: self._binding(plan, task, toolchain, reflection, observations),
                        execute, reuse=current.get('reflective_imports') is not None)
                else:
                    result = executor.run(task, task_directory)
                if observe_toolchain:
                    self._task_toolchain(task, toolchain, observations)
                self.verify_task(plan, task, result, toolchain, reflection, observations)
                self._observe_inputs(task, observations)
                if kind == 'environment':
                    reflection = self._reflection(result, toolchain, observations)
                    executor.artifact_hasher = observations.hash_file
                observations.assert_stable()
                record['tasks'].append({'id': task['id'], 'specification': digest(task), 'result': result})
                write_json(state / (phase + '.json'), record)
            self.validate_plan(plan)
            observations.assert_stable()
            if observe_toolchain and self.runtime.compiler_identity(observations.hash_file) != toolchain:
                raise ValueError('Native toolchain changed during phase execution')
            record.update(status='completed', toolchain=toolchain)
            write_json(state / (phase + '.json'), record)
            return record

    def verify_phase(self, state, plan, phase, toolchain, observations=None, *, observe_toolchain=False):
        state = self._external(state)
        record = read_json(state / (phase + '.json'))
        if (not isinstance(record, dict) or record.get('schema') != SCHEMA
                or record.get('plan_id') != plan['id'] or record.get('phase') != phase
                or record.get('status') != 'completed' or not isinstance(record.get('directory'), str)):
            raise ValueError('Missing/incomplete/wrong-plan required CI phase: ' + phase)
        directory = Path(record['directory']).resolve()
        if not directory.is_relative_to(state / 'runs'):
            raise ValueError('Phase evidence escaped its invocation')
        required = self._tasks(plan, phase, directory)
        actual = record.get('tasks')
        if not isinstance(actual, list) or len(actual) != len(required):
            raise ValueError('Required phase task coverage is incomplete: ' + phase)
        if phase == 'native' and record.get('toolchain') != toolchain:
            raise ValueError('Native toolchain changed since execution')
        observations = observations or self._source_observer(plan)
        reflection = None
        for task, item in zip(required, actual):
            if (not isinstance(item, dict) or item.get('id') != task['id']
                    or item.get('specification') != digest(task)):
                raise ValueError('Wrong/forged phase task specification: ' + task['id'])
            if phase == 'native' and observe_toolchain:
                self._task_toolchain(task, toolchain, observations)
            self.verify_task(plan, task, item.get('result'), toolchain, reflection, observations)
            self._observe_inputs(task, observations)
            if task['kind'] == 'environment':
                reflection = self._reflection(item['result'], toolchain, observations)
        observations.assert_stable()
        return record

    def finalize(self, state, outputs=None, toolchain=None):
        state = self._external(state)
        outputs = self._external(outputs) if outputs is not None else None
        with locked(state):
            (state / 'complete.json').unlink(missing_ok=True)
            if outputs:
                outputs.unlink(missing_ok=True)
                outputs.with_suffix(outputs.suffix + '.coverage.json').unlink(missing_ok=True)
            plan = read_json(state / 'plan.json')
            self.validate_plan(plan)
            observations = self._source_observer(plan)
            observe_toolchain = toolchain is None and 'native' in plan['required_phases']
            if observe_toolchain:
                toolchain = self.runtime.compiler_identity(observations.hash_file)
            records = [self.verify_phase(state, plan, phase, toolchain if phase == 'native' else None,
                                         observations, observe_toolchain=observe_toolchain)
                       for phase in plan['required_phases']]
            self.validate_plan(plan)
            outcomes = [item for record in records for item in record['tasks']]
            checks = []
            for record in records:
                required = self._tasks(plan, record['phase'], Path(record['directory']))
                checks.extend(item for task, item in zip(required, record['tasks']) if task['kind'] == 'check')
            summary = {'schema': SCHEMA, 'status': 'complete', 'plan_id': plan['id'],
                       'implementation': plan['implementation'],
                       'head': plan['head'], 'baseline': plan.get('baseline'),
                       'required_phases': plan['required_phases'],
                       'performed_phases': [record['phase'] for record in records],
                       'performed_checks': [item['id'] for item in checks if item['result']['mode'] == 'performed'],
                       'reused_checks': [item['id'] for item in checks if item['result']['mode'] == 'reused'],
                       'compiled_or_refreshed_targets': sorted({name for item in outcomes
                           for name in item['result'].get('compiled_or_refreshed', [])}),
                       'reused_build_targets': sorted({name for item in outcomes
                           for name in item['result'].get('reused_build_targets', [])})}
            hook = getattr(self.adapter, 'summary', None)
            if hook:
                extra = hook(self.root, plan, records)
                if not isinstance(extra, dict) or SUMMARY_FIELDS.intersection(extra):
                    raise ValueError('Adapter summary attempted to override core completion fields')
                summary.update(extra)
            observations.assert_stable()
            if outputs and 'native' in plan['required_phases']:
                native = next(record for record in records if record['phase'] == 'native')
                mappings = [Path(task['mapping']) for task in
                            self._tasks(plan, 'native', Path(native['directory'])) if task.get('mapping')]
                if len(mappings) != 1:
                    raise ValueError('Publishing requires one validated native mapping task')
                outputs.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(mappings[0], outputs)
                write_json(outputs.with_suffix(outputs.suffix + '.coverage.json'), summary)
            observations.assert_stable()
            write_json(state / 'complete.json', summary)
            return summary
