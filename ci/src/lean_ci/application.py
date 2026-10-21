"""Repository-independent CI lifecycle with strict, reconstructed coverage.

Adapters are trusted committed policy. They choose coverage and check inputs;
this module alone admits receipts, phase completion and publication. Progress
records are compatibility evidence from a trusted producer, not signatures.
"""
from contextlib import contextmanager
import json
import os
from pathlib import Path
import subprocess
import uuid

from .execution.runtime import NativeRuntime
from .execution.runner import TaskRunner, STANDARD_KINDS
from .execution.state import (Progress, ReflectionGraph, ReflectionUnavailable, TemporalInputs,
    digest, file_hash, module_identity, read_json, valid_receipt, valid_success, write_json)

SCHEMA = 1
PLAN_FIELDS = {'schema', 'id', 'invocation', 'head', 'repository', 'source_files', 'required_phases', 'implementation'}
SUMMARY_FIELDS = {'mapping_groups', 'mapping_status', 'implementation', 'schema', 'status', 'plan_id', 'head', 'baseline', 'required_phases',
                  'performed_phases', 'performed_checks', 'reused_checks',
                  'compiled_or_refreshed_targets', 'reused_build_targets', 'execution_diagnostics'}


def _implementation_owners():
    directory = Path(__file__).absolute().parent
    return tuple(sorted(path.relative_to(directory).as_posix()
                        for path in directory.rglob('*')
                        if path.is_file() and path.suffix in {'.py', '.lean'}
                        and '__pycache__' not in path.parts))


IMPLEMENTATION_OWNERS = _implementation_owners()


def implementation_sources():
    """Actual installed package owners, independent of any repository copy."""
    directory = Path(__file__).absolute().parent
    return {name: directory / name for name in _implementation_owners()}


def implementation_identity(observations=None):
    """Content-only identity; paths and temporal stamps never enter reuse keys."""
    hash_file = observations.hash_file if observations is not None else file_hash
    return {name: hash_file(path) for name, path in sorted(implementation_sources().items())}


def git(root, *arguments):
    return subprocess.check_output(['git', *arguments], cwd=root,
                                   env=dict(os.environ, GIT_OPTIONAL_LOCKS='0'))


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


class Application(TaskRunner):
    """Small policy interface: plan, required_phases, validate_plan, tasks, binding.

    Optional hooks: custom_task/verify_custom_task, observe_inputs, summary.
    Tasks setting establishes_inputs=True trigger observe_inputs after setup.
    binding must return the state's standard check-binding schema, including
    arguments and reflective_imports. Unsupported reflection disables reuse.
    """
    def __init__(self, root, adapter, runtime=None, *, package_cwd=None):
        self.root = Path(root).resolve()
        self.adapter = adapter
        self.package_cwd = Path(package_cwd or (runtime.root if runtime else self.root)).resolve()
        if not self.package_cwd.is_relative_to(self.root):
            raise ValueError('Lake package working directory must be inside its repository')
        self.runtime = runtime or NativeRuntime(self.package_cwd)

    def check(self, state=None, requested_base=None, targets=(), progress=None, outputs=None,
              *, executor=None, toolchain=None):
        """Scoped working-tree final validation; no committed CI plan is created."""
        from .execution.local import check
        return check(self, state, requested_base, targets, progress, outputs,
                     executor=executor, toolchain=toolchain)

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
            observe_toolchain = toolchain is None and phase == 'native'
            if observe_toolchain:
                toolchain = self.runtime.compiler_identity(observations.hash_file, cwd=self.package_cwd)
            def save_task(item):
                record['tasks'].append(item)
                write_json(state / (phase + '.json'), record)
            self.run_tasks(plan, required, directory, progress, toolchain, observations,
                           executor, observe_toolchain=observe_toolchain, record_task=save_task)
            self.validate_plan(plan)
            observations.assert_stable()
            if observe_toolchain and self.runtime.compiler_identity(observations.hash_file, cwd=self.package_cwd) != toolchain:
                raise ValueError('Native toolchain changed during phase execution')
            record.update(status='completed', toolchain=toolchain,
                          execution_diagnostics=self.execution_diagnostics())
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
        self.verify_tasks(plan, required, actual, toolchain, observations,
                          observe_toolchain=phase == 'native' and observe_toolchain)
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
                toolchain = self.runtime.compiler_identity(observations.hash_file, cwd=self.package_cwd)
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
                           for name in item['result'].get('reused_build_targets', [])}),
                       'execution_diagnostics': self.execution_diagnostics()}
            hook = getattr(self.adapter, 'summary', None)
            if hook:
                extra = hook(self.root, plan, records)
                if not isinstance(extra, dict) or SUMMARY_FIELDS.intersection(extra):
                    raise ValueError('Adapter summary attempted to override core completion fields')
                summary.update(extra)
            self.assert_verified_inputs(observations)
            if outputs and 'native' in plan['required_phases']:
                native = next(record for record in records if record['phase'] == 'native')
                from .transport.mappings import export_mappings
                producers = [(task, item['result']) for task, item in zip(
                    self._tasks(plan, 'native', Path(native['directory'])), native['tasks'])
                    if task.get('mapping')]
                if producers:
                    summary['mapping_groups'] = export_mappings(producers, outputs, toolchain, observations,
                        repository_root=self.root)
                    summary['mapping_status'] = 'qualified-build-outputs'
                    write_json(outputs.with_suffix(outputs.suffix + '.coverage.json'), summary)
                else:
                    summary.update(mapping_groups=[], mapping_status='no-new-build-outputs')
            self.assert_verified_inputs(observations)
            write_json(state / 'complete.json', summary)
            return summary
