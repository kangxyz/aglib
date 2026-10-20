"""Bounded overlap of explicitly independent read-only native checks.

Only NativeRuntime.run executes in workers. Bindings, temporal observations,
progress records and callbacks belong to the calling thread. This helper never
creates subprocesses or changes the runtime's environment/resource policy.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from threading import Event

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
    if (not isinstance(declaration, dict)
            or set(declaration) != {'id', 'jobs', 'read_only', 'single_process'}
            or not isinstance(declaration['id'], str) or not declaration['id']
            or type(declaration['jobs']) is not int or declaration['jobs'] < 1
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
