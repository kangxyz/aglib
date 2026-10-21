"""Working-tree source boundary for the shared final-check task executor."""
from pathlib import Path
import tempfile
import uuid

from ..application import git, implementation_identity, locked
from .state import TemporalInputs, digest, write_json
from ..transport.mappings import export_mappings


RESERVED = {'schema', 'id', 'invocation', 'repository', 'source_files', 'source_basis', 'implementation'}


def observe_paths(root, paths, observations):
    result = {}
    for entry in paths:
        value = entry['path'] if isinstance(entry, dict) else str(entry)
        path = (root / value).absolute()
        if not path.resolve().is_relative_to(root):
            raise ValueError('Local source input escaped its repository: ' + value)
        relative = path.relative_to(root).as_posix()
        if path.is_dir():
            excluded = entry.get('exclude', ()) if isinstance(entry, dict) else ()
            inventory = observations.observe_directory(path, excluded)
            result[relative] = {'directory': True, 'exclude': sorted(excluded),
                                'entries': inventory[1]}
        else:
            if isinstance(entry, dict) and entry.get('exclude'):
                raise ValueError('Only directory enrollment inputs accept exclusions')
            result[relative] = observations.optional_hash(path)
    return result


def observe_git_basis(root, observations):
    """Guard mutable Git selectors; object ids keep immutable history explicit."""
    names = ['HEAD', 'index', 'packed-refs', 'info/exclude']
    symbolic = git(root, 'rev-parse', '--symbolic-full-name', 'HEAD').decode().strip()
    if symbolic.startswith('refs/'):
        names.append(symbolic)
    for name in names:
        value = git(root, 'rev-parse', '--git-path', name).decode().strip()
        path = Path(value)
        observations.optional_hash(path if path.is_absolute() else root / path)


def check(application, state=None, requested_base=None, targets=(), progress=None, outputs=None,
          *, executor=None, toolchain=None):
    root, adapter = application.root, application.adapter
    state = (application._external(state) if state is not None else
             Path(tempfile.mkdtemp(prefix='lean-ci-check-')).resolve())
    state.mkdir(parents=True, exist_ok=True)
    progress = application._external(progress or state / 'check-progress')
    outputs = application._external(outputs) if outputs is not None else None
    with locked(state):
        (state / 'complete.json').unlink(missing_ok=True)
        if outputs is not None:
            outputs.unlink(missing_ok=True)
            outputs.with_suffix(outputs.suffix + '.coverage.json').unlink(missing_ok=True)
        observations = getattr(application, '_local_loader_observations', None) or TemporalInputs()
        if hasattr(application, '_local_loader_observations'):
            del application._local_loader_observations
        implementation = implementation_identity(observations)
        observe_git_basis(root, observations)
        source_basis = {'kind': 'working-tree', 'head': git(root, 'rev-parse', 'HEAD').decode().strip()}
        enroll = getattr(adapter, 'local_inputs', None)
        selector = getattr(adapter, 'select_scope', None)
        if enroll is None or selector is None:
            raise ValueError('Local final checks require local_inputs and select_scope adapter hooks')
        # The inventory hook is trusted source policy, not an affected selector.
        # Observe all candidate bytes before selection or cheap source checks.
        paths = enroll(root, requested_base=requested_base, targets=list(targets))
        if not isinstance(paths, (list, tuple, set)):
            raise ValueError('local_inputs must return explicit scoped input paths')
        sources = observe_paths(root, paths, observations)
        observations.assert_stable()
        payload = selector(root, requested_base=requested_base, targets=list(targets),
                           source_basis=source_basis)
        if not isinstance(payload, dict) or RESERVED.intersection(payload):
            raise ValueError('Local selector attempted to override source boundary fields')
        plan = dict(payload, schema=1, invocation=uuid.uuid4().hex, source_basis=source_basis,
                    repository=str(root), source_files=sources, implementation=implementation)
        plan['id'] = digest(plan)
        validate = getattr(adapter, 'validate_local', None)
        if validate:
            validate(root, plan)
        observations.assert_stable()
        directory = state / 'runs' / ('check-' + plan['invocation'])
        directory.mkdir(parents=True)
        required = application._tasks(plan, 'check', directory)
        observations.assert_stable()
        # Source-only checks require no compiler discovery. Native graphs and
        # check environments use the package cwd, independently of the Git root.
        first_native = next((i for i, task in enumerate(required)
                             if task['kind'] in ('build', 'graph-build', 'environment')
                             or task.get('native')
                             or (task['kind'] == 'check' and task.get('native') is not False
                                 and not task.get('input_boundary'))), len(required))
        record = {'schema': 1, 'status': 'running', 'source_basis': source_basis,
                  'source_files': sources, 'implementation': implementation, 'tasks': [],
                  'directory': str(directory), 'plan_id': plan['id']}
        receipt_path = state / 'local.json'
        def save(item):
            record['tasks'].append(item)
            write_json(receipt_path, record)
        write_json(receipt_path, record)
        observe_toolchain = toolchain is None and first_native < len(required)
        if observe_toolchain:
            toolchain = application.runtime.compiler_identity(observations.hash_file, cwd=application.package_cwd)
        application.run_tasks(plan, required, directory, progress,
                              toolchain, observations, executor, observe_toolchain=observe_toolchain,
                              record_task=save)
        # Reconstruct policy and validate the same record before releasing success.
        reconstructed = application._tasks(plan, 'check', directory)
        application.verify_tasks(plan, reconstructed, record['tasks'], toolchain, observations,
                                 observe_toolchain=observe_toolchain)
        if validate:
            validate(root, plan)
        observations.assert_stable()
        if git(root, 'rev-parse', 'HEAD').decode().strip() != source_basis['head']:
            raise ValueError('Local selection HEAD changed during final checks')
        if observe_toolchain and application.runtime.compiler_identity(
                observations.hash_file, cwd=application.package_cwd) != toolchain:
            raise ValueError('Native toolchain changed during local final checks')
        checks = [item for task, item in zip(required, record['tasks']) if task['kind'] == 'check']
        summary = {'schema': 1, 'status': 'complete', 'source_basis': source_basis,
                   'source_files': sources, 'implementation': implementation,
                   'directory': str(state), 'toolchain': toolchain,
                   'performed_checks': [item['id'] for item in checks if item['result']['mode'] == 'performed'],
                   'reused_checks': [item['id'] for item in checks if item['result']['mode'] == 'reused'],
                   'compiled_or_refreshed_targets': sorted({n for item in record['tasks']
                        for n in item['result'].get('compiled_or_refreshed', ())}),
                   'reused_build_targets': sorted({n for item in record['tasks']
                        for n in item['result'].get('reused_build_targets', ())}),
                   'execution_diagnostics': application.execution_diagnostics()}
        hook = getattr(adapter, 'local_summary', None)
        if hook:
            extra = hook(root, plan, record)
            if not isinstance(extra, dict) or set(summary).intersection(extra) or 'mapping_groups' in extra:
                raise ValueError('Adapter local summary attempted to override core completion fields')
            summary.update(extra)
        if outputs is not None and first_native < len(required):
            producers = [(task, item['result']) for task, item in zip(required, record['tasks'])
                         if task.get('mapping')]
            if producers:
                summary['mapping_groups'] = export_mappings(producers, outputs, toolchain, observations,
                        repository_root=root)
                summary['mapping_status'] = 'qualified-build-outputs'
                write_json(outputs.with_suffix(outputs.suffix + '.coverage.json'), summary)
            else:
                summary.update(mapping_groups=[], mapping_status='no-new-build-outputs')
        application.assert_verified_inputs(observations)
        record.update(status='completed', toolchain=toolchain)
        write_json(receipt_path, record)
        write_json(state / 'complete.json', summary)
        return summary
