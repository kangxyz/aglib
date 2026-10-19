"""Shared task execution and reconstructed receipt validation.

Repository adapters declare trusted policy. This runner shares mechanics between
strict committed CI and scoped working-tree final checks, without changing either
source boundary.
"""
from pathlib import Path

from .runtime import command_matches, parse_search_path
from .state import (InputDrift, Progress, ReflectionGraph, ReflectionUnavailable, digest,
                    module_identity, valid_receipt, valid_success)

STANDARD_KINDS = {'process', 'build', 'graph-build', 'environment', 'check'}


def reusable_check(task, binding):
    # A nonreflective source/control check must deliberately declare its complete
    # boundary. Plain processes never acquire reusable success semantics.
    return (binding.get('reflective_imports') is not None or
            (bool(task.get('input_boundary')) and isinstance(binding.get('raw_inputs'), dict)))


class TaskRunner:
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
            if not Path(task['cwd']).resolve().is_relative_to(self.root):
                raise ValueError('Task working directory must be inside its repository')
            identifiers.add(task['id'])
        return tasks

    def _observe_inputs(self, task, observations):
        try:
            for value in task.get('established_paths', ()):
                path = (self.root / value).absolute()
                if not path.resolve().is_relative_to(self.root):
                    raise ValueError('Established input escaped its repository')
                observations.optional_hash(path)
            if task.get('establishes_inputs'):
                hook = getattr(self.adapter, 'observe_inputs', None)
                if hook:
                    hook(self.root, observations)
            observations.assert_stable()
        except InputDrift as error:
            if task.get('establishes_inputs') or task.get('established_paths'):
                raise InputDrift(str(error) + '; deterministic ignored .lake directories/links '
                    'must be prepared before a local final check; keep tracked manifests and pins unchanged') from error
            raise

    def _binding(self, plan, task, toolchain, reflection, observations):
        observations.assert_stable()
        cwd = Path(task['cwd']).resolve()
        if not cwd.is_relative_to(self.root):
            raise ValueError('Check working directory must be inside its repository')
        semantic_toolchain = ({key: value for key, value in (toolchain or {}).items()
                               if key != 'installation'} if task.get('native', True) else {})
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
                              'generated': digest(task['generated']) if task.get('generated') else None,
                              'generated_argument_index': task.get('generated_argument_index', -1),
                              'generated_path': bool(task.get('generated_path')),
                              'input_boundary': task.get('input_boundary'),
                              'declared_environment': {name: self.runtime.environment.get(name)
                                  for name in task.get('environment_keys', ())}}
        observations.assert_stable()
        return value

    def _reflection(self, result, toolchain, observations, cwd=None):
        try:
            return ReflectionGraph(Path(cwd or self.package_cwd), result['search_path'], toolchain, observations=observations)
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
                    or (result['mode'] == 'reused' and not reusable_check(task, current))):
                raise ValueError('Missing/stale/corrupt individual check success: ' + task['id'])
            receipt = result['success']['receipt']
            if (not isinstance(receipt.get('cwd'), str) or not Path(receipt['cwd']).is_absolute()
                    or (result['mode'] == 'performed' and not valid_receipt(receipt, cwd=task['cwd']))):
                raise ValueError('Wrong check receipt working directory: ' + task['id'])
            actual, expected = list(receipt['command']), list(task['command'])
            if task.get('generated') and result['mode'] == 'reused':
                index = task.get('generated_argument_index', -1)
                actual[index] = expected[index]
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

    def run_tasks(self, plan, required, directory, progress, toolchain, observations,
                  executor=None, *, observe_toolchain=False, record_task=None):
        executor = executor or self.runtime
        progress_store = Progress(progress)
        reflections, outcomes = {}, []
        for index, task in enumerate(required):
            task_directory = directory / f'task-{index:04d}'
            kind, cwd = task['kind'], str(Path(task['cwd']).resolve())
            reflection = reflections.get(cwd)
            if observe_toolchain and task.get('native', True):
                self._task_toolchain(task, toolchain, observations)
            if kind not in STANDARD_KINDS:
                handler = getattr(self.adapter, 'custom_task', None)
                if handler is None:
                    raise ValueError('No custom task executor: ' + kind)
                result = handler(self.root, plan, task, task_directory)
            elif kind == 'check':
                def execute(task=task, task_directory=task_directory):
                    evidence = executor.run(task, task_directory)
                    if observe_toolchain and task.get('native', True):
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
                    execute, reuse=reusable_check(task, current))
            else:
                result = executor.run(task, task_directory)
            if observe_toolchain and task.get('native', True):
                self._task_toolchain(task, toolchain, observations)
            self.verify_task(plan, task, result, toolchain, reflection, observations)
            self._observe_inputs(task, observations)
            if kind == 'environment':
                reflections[cwd] = self._reflection(result, toolchain, observations, cwd)
                executor.artifact_hasher = observations.hash_file
            observations.assert_stable()
            item = {'id': task['id'], 'specification': digest(task), 'result': result}
            outcomes.append(item)
            if record_task:
                record_task(item)
        return outcomes

    def verify_tasks(self, plan, required, actual, toolchain, observations, *, observe_toolchain=False):
        if not isinstance(actual, list) or len(actual) != len(required):
            raise ValueError('Required phase task coverage is incomplete')
        reflections = {}
        for task, item in zip(required, actual):
            if (not isinstance(item, dict) or item.get('id') != task['id']
                    or item.get('specification') != digest(task)):
                raise ValueError('Wrong/forged phase task specification: ' + task['id'])
            if observe_toolchain and task.get('native', True):
                self._task_toolchain(task, toolchain, observations)
            cwd = str(Path(task['cwd']).resolve())
            self.verify_task(plan, task, item.get('result'), toolchain, reflections.get(cwd), observations)
            self._observe_inputs(task, observations)
            if task['kind'] == 'environment':
                reflections[cwd] = self._reflection(item['result'], toolchain, observations, cwd)
        observations.assert_stable()
