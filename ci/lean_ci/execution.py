"""Shared task execution and reconstructed receipt validation.

Repository adapters declare trusted policy. This runner shares mechanics between
strict committed CI and scoped working-tree final checks, without changing either
source boundary.
"""
from contextlib import contextmanager, nullcontext
from pathlib import Path
from time import perf_counter

from .batch import check_group, run_checks
from .runtime import command_matches, parse_search_path, semantic_environment, semantic_toolchain
from .state import (CheckInputs, InputDrift, Progress, ReflectionGraph, ReflectionUnavailable, digest,
                    module_identity, valid_receipt, valid_success)

STANDARD_KINDS = {'process', 'build', 'graph-build', 'environment', 'check'}


def reusable_check(task, binding):
    # A nonreflective source/control check must deliberately declare its complete
    # boundary. Plain processes never acquire reusable success semantics.
    return (binding.get('reflective_imports') is not None or
            (bool(task.get('input_boundary')) and isinstance(binding.get('raw_inputs'), dict)))


class TaskRunner:
    @contextmanager
    def _measured(self, name):
        measurements = self.__dict__.setdefault('_measurements', {})
        started = perf_counter()
        try:
            yield
        finally:
            value = measurements.setdefault(name, {'calls': 0, 'seconds': 0.0})
            value['calls'] += 1
            value['seconds'] += perf_counter() - started

    def execution_diagnostics(self):
        """Observed costs only; inclusive guard/binding times must not be added."""
        observations = getattr(self, '_diagnostic_source', None)
        if observations is not None:
            self._guard_measurements['source'] = {'scans': observations.scan_count,
                'seconds': observations.scan_seconds, 'files': len(observations.files),
                'components': len(observations.components)}
        return {'operations': self.__dict__.get('_measurements', {}),
                'guards': self.__dict__.get('_guard_measurements', {}),
                'semantics': 'operation times are inclusive; parallel command times are summed'}

    def assert_verified_inputs(self, observations):
        current = getattr(self, '_verified_inputs', None)
        if current is not None:
            if current.whole is not observations:
                raise ValueError('Verification inputs belong to another source observation')
            current.whole.assert_stable()
            current.native.refresh_link_metadata()
            current.assert_stable()
        else:
            observations.assert_stable()

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
        inspection = getattr(observations, 'inspection', nullcontext)
        with self._measured('binding'), inspection():
            return self._binding_value(plan, task, toolchain, reflection, observations)

    def _binding_value(self, plan, task, toolchain, reflection, observations):
        cwd = Path(task['cwd']).resolve()
        if not cwd.is_relative_to(self.root):
            raise ValueError('Check working directory must be inside its repository')
        semantic = semantic_toolchain(toolchain) if task.get('native', True) else {}
        value = self.adapter.binding(self.root, task, semantic, reflection=reflection,
                                     observations=observations)
        if not isinstance(value, dict) or not isinstance(value.get('arguments'), list):
            raise ValueError('Adapter omitted required check binding')
        # Bind the execution mechanics independently of repository policy fields.
        value = dict(value)
        if isinstance(value.get('environment'), dict) and task.get('native', True):
            value['environment'] = semantic_environment(value['environment'], toolchain)
        value['execution'] = {'cwd': cwd.relative_to(self.root).as_posix(),
                              'repository': plan['repository'], 'implementation': plan['implementation'],
                              'kind': task['kind'],
                              'capped': bool(task.get('capped')),
                              'toolchain': semantic,
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
            return ReflectionGraph(Path(cwd or self.package_cwd), result['search_path'],
                                   semantic_toolchain(toolchain, installation=True), observations=observations)
        except ReflectionUnavailable:
            return None

    def _task_toolchain(self, task, expected, observations):
        actual = self.runtime.compiler_identity(observations.hash_file, cwd=task['cwd'])
        if actual != expected:
            raise ValueError('Mixed native compiler/runtime identities are unsupported: ' + task['cwd'])
        observations.assert_stable()

    def verify_task(self, plan, task, result, toolchain, reflection, observations, *, current_binding=None):
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
            current = (current_binding if current_binding is not None else
                       self._binding(plan, task, toolchain, reflection, observations))
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
                name: module_identity(Path(task['cwd']), name,
                    getattr(observations, 'native_hash_file', observations.hash_file))
                for name in task['identity_modules']}:
            raise ValueError('Current complete native graph outputs drifted: ' + task['id'])
        if kind == 'environment':
            path = Path(task['environment_output'])
            if (result.get('output_sha256') != observations.hash_file(path)
                    or result.get('search_path') != parse_search_path(path.read_text())):
                raise ValueError('Wrong/missing actual native import search-path evidence')

    def run_tasks(self, plan, required, directory, progress, toolchain, observations,
                  executor=None, *, observe_toolchain=False, record_task=None):
        self._measurements, self._guard_measurements = {}, {}
        self._verified_inputs = None
        with self._measured('run_tasks'):
            return self._run_tasks(plan, required, directory, progress, toolchain, observations,
                                   executor, observe_toolchain=observe_toolchain, record_task=record_task)

    def _run_tasks(self, plan, required, directory, progress, toolchain, observations,
                   executor=None, *, observe_toolchain=False, record_task=None):
        self._diagnostic_source = observations
        executor = executor or self.runtime
        progress_store = Progress(progress)
        searches, outcomes = {}, {}
        hash_cache, metadata_cache = {}, {}
        self._native_hash_cache, self._native_metadata_cache = hash_cache, metadata_cache
        next_record = 0

        def retire(inputs):
            if isinstance(inputs, CheckInputs):
                row = self._guard_measurements.setdefault('native_execution', {'scans': 0, 'seconds': 0.0})
                row['scans'] += inputs.native.scan_count
                row['seconds'] += inputs.native.scan_seconds
                row['max_files'] = max(row.get('max_files', 0), len(inputs.native.files))
                row['max_components'] = max(row.get('max_components', 0), len(inputs.native.components))
            self._guard_measurements['source'] = {'scans': observations.scan_count,
                                                  'seconds': observations.scan_seconds}

        def context(task):
            inputs = (CheckInputs(observations, hash_cache=hash_cache, metadata_cache=metadata_cache)
                      if task.get('native', True) else observations)
            cwd = str(Path(task['cwd']).resolve())
            reflection = (self._reflection({'search_path': searches[cwd]}, toolchain, inputs, cwd)
                          if cwd in searches else None)
            return inputs, reflection

        def record(index, task, result):
            nonlocal next_record
            item = {'id': task['id'], 'specification': digest(task), 'result': result}
            outcomes[index] = item
            # Keep the existing ordered record protocol. Independent successes
            # beyond a failed prefix remain in Progress for the next invocation.
            while next_record in outcomes:
                if record_task:
                    with self._measured('record_write'):
                        record_task(outcomes[next_record])
                next_record += 1

        def checked_receipt(task, evidence):
            if (not isinstance(evidence, dict)
                    or not valid_receipt(evidence.get('receipt'), cwd=task['cwd'])
                    or not command_matches(task['command'], evidence['receipt']['command'])):
                raise ValueError('Check command omitted its actual validated receipt')
            return evidence['receipt'], evidence['receipt']['command']

        def complete(index, task, result, inputs, reflection, current=None):
            if observe_toolchain and task.get('native', True):
                self._task_toolchain(task, toolchain, observations)
            self.verify_task(plan, task, result, toolchain, reflection, inputs, current_binding=current)
            self._observe_inputs(task, inputs)
            inputs.assert_stable()
            record(index, task, result)
            retire(inputs)

        index = 0
        while index < len(required):
            task = required[index]
            if task.get('check_batch') is not None:
                group_end = index + 1
                label = task['check_batch'].get('id') if isinstance(task['check_batch'], dict) else None
                while (group_end < len(required)
                       and isinstance(required[group_end].get('check_batch'), dict)
                       and required[group_end]['check_batch'].get('id') == label):
                    group_end += 1
                group = required[index:group_end]
                jobs = check_group(group, self.runtime)
                contexts = {}

                def pending():
                    for position in range(index, group_end):
                        member = required[position]
                        if observe_toolchain:
                            self._task_toolchain(member, toolchain, observations)
                        inputs, reflection = context(member)
                        before = self._binding(plan, member, toolchain, reflection, inputs)
                        prior = progress_store.lookup(before) if reusable_check(member, before) else None
                        if prior is not None:
                            after = self._binding(plan, member, toolchain, reflection, inputs)
                            if after != before:
                                raise ValueError('Check inputs drifted while reading reusable success')
                            complete(position, member, {'mode': 'reused', 'success': prior},
                                     inputs, reflection, after)
                        else:
                            contexts[position] = (inputs, reflection, before)
                            yield position, member, directory / f'task-{position:04d}'

                def accept(position, evidence):
                    member = required[position]
                    inputs, reflection, before = contexts.pop(position)
                    receipt, command = checked_receipt(member, evidence)
                    elapsed = receipt.get('duration_seconds')
                    if isinstance(elapsed, (int, float)) and not isinstance(elapsed, bool) and elapsed >= 0:
                        measured = self._measurements.setdefault('batch_command_receipts', {'calls': 0, 'seconds': 0.0})
                        measured['calls'] += 1
                        measured['seconds'] += elapsed
                    if observe_toolchain:
                        self._task_toolchain(member, toolchain, observations)
                    after = self._binding(plan, member, toolchain, reflection, inputs)
                    if after != before:
                        raise ValueError('Check inputs drifted during execution; success was not recorded')
                    success = progress_store.save(before, receipt, command)
                    complete(position, member, {'mode': 'performed', 'success': success},
                             inputs, reflection, after)

                with self._measured('check_batch'):
                    run_checks(executor, pending(), jobs, accept)
                index = group_end
                continue
            task_directory = directory / f'task-{index:04d}'
            kind, cwd = task['kind'], str(Path(task['cwd']).resolve())
            inputs, reflection = context(task)
            executor.artifact_hasher = getattr(inputs, 'native_hash_file', inputs.hash_file)
            if observe_toolchain and task.get('native', True):
                self._task_toolchain(task, toolchain, observations)
            current = None
            if kind not in STANDARD_KINDS:
                handler = getattr(self.adapter, 'custom_task', None)
                if handler is None:
                    raise ValueError('No custom task executor: ' + kind)
                with self._measured('custom_task'):
                    result = handler(self.root, plan, task, task_directory)
            elif kind == 'check':
                def binding():
                    nonlocal current
                    current = self._binding(plan, task, toolchain, reflection, inputs)
                    return current

                def execute(task=task, task_directory=task_directory):
                    with self._measured('command'):
                        evidence = executor.run(task, task_directory)
                    if observe_toolchain and task.get('native', True):
                        self._task_toolchain(task, toolchain, observations)
                    inputs.assert_stable()
                    return checked_receipt(task, evidence)
                result = progress_store.run(binding, execute,
                                            reuse=lambda value: reusable_check(task, value))
            else:
                with self._measured('command'):
                    result = executor.run(task, task_directory)
            if kind == 'environment':
                searches[cwd] = result['search_path']
            complete(index, task, result, inputs, reflection, current)
            index += 1
        return [outcomes[position] for position in range(len(required))]

    def verify_tasks(self, plan, required, actual, toolchain, observations, *, observe_toolchain=False):
        with self._measured('verify_tasks'):
            return self._verify_tasks(plan, required, actual, toolchain, observations,
                                      observe_toolchain=observe_toolchain)

    def _verify_tasks(self, plan, required, actual, toolchain, observations, *, observe_toolchain=False):
        self._diagnostic_source = observations
        if not isinstance(actual, list) or len(actual) != len(required):
            raise ValueError('Required phase task coverage is incomplete')
        inputs = CheckInputs(observations,
            hash_cache=getattr(self, '_native_hash_cache', None),
            metadata_cache=getattr(self, '_native_metadata_cache', None))
        self._verified_inputs = inputs
        reflections = {}
        # This pass only reads receipts and bindings. Keep per-file observations,
        # but scan the complete growing import closure once at its boundary.
        with inputs.inspection():
            for task, item in zip(required, actual):
                if (not isinstance(item, dict) or item.get('id') != task['id']
                        or item.get('specification') != digest(task)):
                    raise ValueError('Wrong/forged phase task specification: ' + task['id'])
                if observe_toolchain and task.get('native', True):
                    self._task_toolchain(task, toolchain, observations)
                cwd = str(Path(task['cwd']).resolve())
                self.verify_task(plan, task, item.get('result'), toolchain, reflections.get(cwd), inputs)
                self._observe_inputs(task, inputs)
                if task['kind'] == 'environment':
                    reflections[cwd] = self._reflection(item['result'], toolchain, inputs, cwd)
        self._guard_measurements = getattr(self, '_guard_measurements', {})
        self._guard_measurements['native_verification'] = {'scans': inputs.native.scan_count,
            'seconds': inputs.native.scan_seconds, 'files': len(inputs.native.files),
            'components': len(inputs.native.components)}
