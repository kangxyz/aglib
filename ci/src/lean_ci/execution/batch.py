"""Bounded overlap of explicitly independent read-only native checks.

Only NativeRuntime.run executes in workers. Bindings, temporal observations,
progress records and callbacks belong to the calling thread. This helper never
creates subprocesses or changes the runtime's environment/resource policy.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from threading import Event
from pathlib import Path
import re
import sys

from ..project.source import IDENT, MODULE

from . import resources


def check_group(tasks, runtime):
    """Validate one adjacent, explicitly declared group and return its job cap.

The trusted adapter promises read-only checks with at most one active compiler
per task. Local policy remains serial. Managed wrappers retain global admission
and enforce their unchanged compiler/resource profile.
    """
    if not tasks:
        raise ValueError('A check batch must contain actual checks')
    declaration = tasks[0].get('check_batch')
    canonical = isinstance(declaration, dict) and declaration.get('mode') == 'canonical-prefix'
    keys = {'id', 'mode', 'read_only', 'single_process'} if canonical else {'id', 'jobs', 'read_only', 'single_process'}
    if (not isinstance(declaration, dict)
            or set(declaration) != keys
            or not isinstance(declaration['id'], str) or not declaration['id']
            or (not canonical and (type(declaration['jobs']) is not int or declaration['jobs'] < 1))
            or declaration['read_only'] is not True or declaration['single_process'] is not True):
        raise ValueError('Malformed explicit read-only check batch')
    forbidden = ('generated', 'generated_path', 'mapping', 'identity_modules',
                 'establishes_inputs', 'established_paths', 'environment_output')
    identifiers = set()
    for task in tasks:
        if (task.get('kind') != 'check' or task.get('check_batch') != declaration
                or task.get('capped') is not True or task.get('native', True) is not True
                or any(task.get(field) for field in forbidden)
                or task.get('id') in identifiers):
            raise ValueError('Only distinct capped read-only native checks may overlap')
        identifiers.add(task.get('id'))
    if canonical:
        bases = [canonical_command(task) for task in tasks]
        if any(base != bases[0] or task['cwd'] != tasks[0]['cwd'] for task, base in zip(tasks, bases)):
            raise ValueError('Canonical batch origins must share their fixed driver/configuration')
        return 1
    profile = resources.remote_profile(runtime.environment, runtime.resource_config)
    ceiling = profile['jobs'] if profile else 1
    if declaration['jobs'] > ceiling:
        raise ValueError('Check batch jobs exceed the admitted native resource profile')
    return declaration['jobs']


def run_checks(executor, pending, jobs, accept):
    """Run (index, task, directory) entries; accept evidence on the caller thread.

At most jobs calls are active. Any failure stops further admission. Active
commands are drained, and their independent successes are still accepted,
before the first error is re-raised. Interruption also sets the cancellation
callback passed to each native monitor, which settles its own process group.
This helper never treats Future.cancel() as subprocess cancellation.
    """
    if type(jobs) is not int or jobs < 1:
        raise ValueError('Check batch jobs must be a positive integer')
    pending = iter(pending)
    active, first_error, cancellation = {}, None, Event()

    def failed(error):
        nonlocal first_error
        first_error = first_error or error
        if not isinstance(error, Exception):
            cancellation.set()

    with ThreadPoolExecutor(max_workers=jobs, thread_name_prefix='lean-check') as pool:
        exhausted = False
        while active or (not exhausted and first_error is None):
            while len(active) < jobs and not exhausted and first_error is None:
                try:
                    index, task, directory = next(pending)
                except StopIteration:
                    exhausted = True
                    break
                except BaseException as error:
                    failed(error)
                    exhausted = True
                    break
                try:
                    active[pool.submit(executor.run, task, directory,
                                       cancelled=cancellation.is_set)] = index
                except BaseException as error:
                    failed(error)
            if not active:
                break
            try:
                ready, _ = wait(active, return_when=FIRST_COMPLETED)
            except BaseException as error:
                failed(error)
                continue
            for future in sorted(ready, key=lambda item: active[item]):
                index = active.pop(future)
                try:
                    accept(index, future.result())
                except BaseException as error:
                    failed(error)
    if first_error is not None:
        raise first_error


# Bound both retained evidence and one native prefix lifetime. This is not a job cap.
CANONICAL_BATCH_SIZE = 8
CANONICAL_BATCH_KINDS = frozenset({'declarations', 'axioms', 'inventory'})


def _fixed_python_command(command):
    """Accept the configured safe-path invocation and exact legacy fixtures."""
    if (not isinstance(command, list) or not command
            or any(not isinstance(arg, str) for arg in command)
            or Path(command[0]).resolve() != Path(sys.executable).resolve()):
        raise ValueError('Canonical batch requires the fixed Python executable')
    return command[:1] + command[2:] if command[1:2] == ['-P'] else command


def canonical_command(task):
    """Only the fixed common native check kinds may acquire batch semantics."""
    command = task.get('command', [])
    normalized = _fixed_python_command(command)
    modules = task.get('modules')
    kind = task.get('check_kind')
    if (kind not in CANONICAL_BATCH_KINDS or not isinstance(modules, list)
            or len(modules) != 1 or not isinstance(modules[0], str)
            or MODULE.fullmatch(modules[0]) is None or len(normalized) != 10
            or normalized[1:6] != ['-m', 'lean_ci.checks.native', kind, '--root', task['cwd']]
            or normalized[6] != '--config' or not Path(normalized[7]).is_absolute()
            or normalized[8:] != ['--modules', *modules]):
        raise ValueError('Canonical batch requires the fixed exact-origin native command')
    return command[:-2]


def selection_item(task, binding):
    from .state import digest
    canonical_command(task)
    name = task['modules'][0]
    return {'id': task['id'], 'module': name,
            'components': [p[1:-1] if p.startswith('«') else p for p in re.findall(IDENT, name)],
            'input_key': digest(binding)}


def valid_batch_evidence(shared):
    """Validate the actual common invocation and its complete flushed sidecar.

    Resource failure can retain a previously completed origin only after the
    owned group is closed. Ordinary exit-zero receipt validation is unchanged.
    These are trusted-producer records, never self-authenticating certificates.
    """
    from .state import digest
    try:
        selection, receipt, records = shared['selection'], shared['receipt'], shared['records']
        command = shared['command']
        normalized = _fixed_python_command(command)
        if (shared['schema'] != 1 or selection['schema'] != 1
                or selection['kind'] not in CANONICAL_BATCH_KINDS
                or not isinstance(selection['invocation'], str) or not selection['invocation']
                or shared['selection_sha256'] != digest(selection)
                or shared['records_sha256'] != digest(records)
                or receipt.get('state') != 'completed' or type(receipt.get('exit_code')) is not int
                or receipt.get('owned_group_gone') is not True
                or 'guard_failure' not in receipt
                or (receipt['guard_failure'] is not None and not isinstance(receipt['guard_failure'], str))
                or not isinstance(receipt.get('cwd'), str) or not Path(receipt['cwd']).is_absolute()
                or receipt.get('command') != command or len(normalized) != 12
                or normalized[1:6] != ['-m', 'lean_ci.checks.native', selection['kind'], '--root', receipt['cwd']]
                or normalized[6] != '--config' or not Path(normalized[7]).is_absolute()
                or normalized[8] != '--selection-json' or not Path(normalized[9]).is_absolute()
                or normalized[10] != '--results-jsonl' or not Path(normalized[11]).is_absolute()
                or not isinstance(selection['items'], list)
                or not 1 <= len(selection['items']) <= CANONICAL_BATCH_SIZE
                or not isinstance(records, list) or len(records) > len(selection['items'])):
            return False
        selected, modules, components = {}, set(), set()
        for item in selection['items']:
            if (set(item) != {'id', 'module', 'components', 'input_key'}
                    or not isinstance(item['id'], str) or not item['id']
                    or item['id'] in selected or item['module'] in modules
                    or not isinstance(item['module'], str) or MODULE.fullmatch(item['module']) is None
                    or item['components'] != [p[1:-1] if p.startswith('«') else p for p in re.findall(IDENT, item['module'])]
                    or re.fullmatch('[0-9a-f]{64}', item['input_key']) is None
                    or tuple(item['components']) in components):
                return False
            selected[item['id']] = item
            modules.add(item['module'])
            components.add(tuple(item['components']))
        seen = set()
        for row in records:
            item = selected.get(row['id'])
            if (item is None or row['id'] in seen or row['invocation'] != selection['invocation']
                    or any(row[k] != item[k] for k in ('module', 'input_key'))
                    or row.get('kind') != selection['kind']
                    or type(row.get('completed')) is not bool or type(row.get('success')) is not bool
                    or (row['success'] and not row['completed'])):
                return False
            seen.add(row['id'])
        return True
    except (KeyError, TypeError, ValueError, AttributeError):
        return False


def valid_batch_success(record, binding):
    from .state import digest
    try:
        shared, item = record['batch'], record['item']
        command = binding['arguments']
        task = {'id': item['id'], 'cwd': shared['receipt']['cwd'],
                'command': command, 'modules': [item['module']],
                'check_kind': shared['selection']['kind']}
        return (record.get('evidence') == 'canonical-prefix-v1'
                and valid_batch_evidence(shared)
                and shared['command'][:-4] == canonical_command(task)
                and item == selection_item(task, binding)
                and item in shared['selection']['items']
                and record['executed_command'] == shared['command']
                and record['receipt'] == shared['receipt']
                and record['result'] in shared['records']
                and record['result']['id'] == item['id']
                and record['result']['input_key'] == digest(binding)
                and record['result']['completed'] is True and record['result']['success'] is True)
    except (KeyError, TypeError, ValueError, AttributeError):
        return False
