"""Execute a frozen native recipe against an admitted, Git-free source snapshot.

The surrounding remote worker owns its workspace lock and expected-source check.
This entry neither acquires that lock nor establishes hosted CI completion.
"""
import argparse
import builtins
from contextlib import contextmanager
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import sysconfig
import tempfile
import uuid

from ..execution import resources
from ..application import Application, implementation_identity, implementation_sources, locked
from .mappings import export_mappings
from ..execution.runtime import semantic_toolchain
from ..execution.state import TemporalInputs, digest, write_json

HASH = re.compile('[0-9a-f]{64}')
RESERVED = {'schema', 'id', 'invocation', 'repository', 'implementation', 'source_basis', 'source_files'}
REQUEST_FIELDS = {'schema', 'adapter', 'payload', 'implementation', 'coordinates', 'policy_inputs',
                  'tooling_files', 'absent_inputs'}
CONFIG_REQUEST_FIELDS = (REQUEST_FIELDS - {'adapter'}) | {'config', 'projection', 'profile'}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON field: ' + key)
        result[key] = value
    return result


def read_observed(path, observations):
    observations.hash_file(path)
    value = json.loads(path.read_text(), object_pairs_hook=unique_object)
    observations.hash_file(path)
    return value


def relative_name(value):
    if (not isinstance(value, str) or not value or '\\' in value
            or any(ord(character) < 32 for character in value)):
        raise ValueError('Expected a safe relative source path')
    path = PurePosixPath(value)
    if (path.is_absolute() or '..' in path.parts or path.as_posix() != value
            or any(part in ('.git', '.lake') for part in path.parts)):
        raise ValueError('Unsafe source path: ' + value)
    return path


def source_path(workspace, name, *, directory=False):
    relative_name(name)
    path = workspace / name
    if not path.resolve().is_relative_to(workspace):
        raise ValueError('Source path escaped its admitted workspace: ' + name)
    for component in [path, *path.parents]:
        if component == workspace:
            break
        if component.is_symlink():
            raise ValueError('Source symlinks are unsupported: ' + name)
    if directory:
        if not path.is_dir():
            raise ValueError('Missing source coordinate directory: ' + name)
    elif not path.is_file():
        raise ValueError('Missing admitted regular source input: ' + name)
    return path


def coordinate(workspace, value):
    if value == '.':
        return workspace
    return source_path(workspace, value, directory=True)


def admit(request_path, source_manifest, expected_source, observations):
    """Admit bytes and declared helper inputs before executing repository policy."""
    if not isinstance(expected_source, str) or HASH.fullmatch(expected_source) is None:
        raise ValueError('Frozen execution requires an exact expected source digest')
    manifest_path = Path(source_manifest).absolute()
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise ValueError('SOURCE.json must be a regular nonsymlink manifest')
    manifest = read_observed(manifest_path, observations)
    if (not isinstance(manifest, dict) or manifest.get('sync_incomplete')
            or manifest.get('content_sha256') != expected_source):
        raise ValueError('Incomplete or wrong expected SOURCE snapshot')
    value = manifest.get('workspace')
    if not isinstance(value, str) or not Path(value).is_absolute():
        raise ValueError('SOURCE requires an absolute workspace owner')
    workspace = Path(value)
    if workspace.resolve() != workspace or not workspace.is_dir():
        raise ValueError('SOURCE workspace must be an existing canonical directory')
    if manifest_path.resolve() != workspace.parent / 'SOURCE.json':
        raise ValueError('SOURCE manifest is outside its workspace owner boundary')
    files = manifest.get('files')
    if (not isinstance(files, dict) or not files or digest(files) != expected_source
            or any(not isinstance(value, str) or HASH.fullmatch(value) is None for value in files.values())):
        raise ValueError('SOURCE canonical files digest or file hash is invalid')
    admitted = {}
    for name, checksum in files.items():
        path = source_path(workspace, name)
        if observations.hash_file(path) != checksum:
            raise ValueError('Admitted source bytes differ from SOURCE: ' + name)
        admitted[path] = checksum
    request_path = Path(request_path).absolute()
    if request_path not in admitted:
        raise ValueError('Frozen request must itself be included in SOURCE.files')
    request = read_observed(request_path, observations)
    if (not isinstance(request, dict) or type(request.get('schema')) is not int
            or request['schema'] not in (1, 2)
            or set(request) - (REQUEST_FIELDS if request['schema'] == 1 else CONFIG_REQUEST_FIELDS)):
        raise ValueError('Unsupported frozen native request schema/fields')
    policy_owner = request['adapter'] if request['schema'] == 1 else request.get('config')
    adapter = source_path(workspace, policy_owner) if request['schema'] == 1 else None
    policy = request.get('policy_inputs')
    if (not isinstance(policy, list) or not policy or policy_owner not in policy
            or any(not isinstance(name, str) for name in policy)):
        raise ValueError('Request must enroll its adapter/configuration and policy/helper inputs explicitly')
    for name in policy:
        if source_path(workspace, name) not in admitted:
            raise ValueError('Policy/helper input is missing from SOURCE.files: ' + name)
    actual = implementation_identity(observations)
    if request.get('implementation') != actual:
        raise ValueError('Installed implementation differs from the frozen request fingerprint')
    tooling = request.get('tooling_files', {})
    if not isinstance(tooling, dict):
        raise ValueError('tooling_files must contain explicit immutable file fingerprints')
    for name, checksum in tooling.items():
        path = Path(name)
        if (not path.is_absolute() or path.resolve() != path or path.is_symlink() or not path.is_file()
                or not isinstance(checksum, str) or HASH.fullmatch(checksum) is None
                or observations.hash_file(path) != checksum):
            raise ValueError('Invalid immutable tooling input: ' + name)
        admitted[path] = checksum
    absent = request.get('absent_inputs', [])
    if not isinstance(absent, list) or any(not isinstance(name, str) for name in absent):
        raise ValueError('absent_inputs must be explicit relative input names')
    for name in absent:
        relative_name(name)
        path = workspace / name
        if not path.resolve().is_relative_to(workspace) or path.exists() or path.is_symlink():
            raise ValueError('Declared absent native input is present or unsafe: ' + name)
        observations.optional_hash(path)
    coordinates = request.get('coordinates')
    if (not isinstance(coordinates, dict) or set(coordinates) != {'root', 'package_cwd', 'source_mapping'}
            or not isinstance(coordinates['source_mapping'], dict)
            or any(not isinstance(k, str) or not isinstance(v, str)
                   for k, v in coordinates['source_mapping'].items())):
        raise ValueError('Request requires explicit source/package coordinates and mapping data')
    root = coordinate(workspace, coordinates['root'])
    package = coordinate(workspace, coordinates['package_cwd'])
    if not package.is_relative_to(root):
        raise ValueError('Native package coordinate escaped its source root')
    package_prefix = package.relative_to(workspace)
    def package_input(name):
        return package_prefix.joinpath(name).as_posix()
    if (any(package_input(name) not in files for name in ('lean-toolchain', 'lake-manifest.json'))
            or not any(package_input(name) in files for name in ('lakefile.toml', 'lakefile.lean'))):
        raise ValueError('Native package pins/configuration must be admitted SOURCE inputs')
    payload = request.get('payload')
    if not isinstance(payload, dict) or RESERVED.intersection(payload):
        raise ValueError('Frozen payload attempted to replace source/runtime envelope fields')
    observations.assert_stable()
    return manifest_path, manifest, request, adapter, root, package, admitted


@contextmanager
def policy_loading(admitted, workspace, observations, directory):
    """Normal Python imports, with actual nonstdlib source origins admitted first."""
    owned = {Path(path).resolve() for path in admitted}
    owned.update(path.resolve() for path in implementation_sources().values())
    stdlib = Path(sysconfig.get_path('stdlib')).resolve()
    sites = {Path(sysconfig.get_path(key)).resolve() for key in ('purelib', 'platlib')}
    def allowed(path):
        return path in owned or (path.is_relative_to(stdlib)
                                and not any(path.is_relative_to(site) for site in sites))
    class SourceAdmission:
        def find_spec(self, fullname, path=None, target=None):
            spec = importlib.machinery.PathFinder.find_spec(fullname, path, target)
            if spec is not None and spec.origin and spec.origin not in ('built-in', 'frozen'):
                origin = Path(spec.origin).resolve()
                if not allowed(origin):
                    raise ValueError('Unadmitted policy/helper import: ' + str(origin))
                if origin in owned:
                    observations.hash_file(origin)
            return spec
    # Avoid retaining an earlier invocation's repository helper module objects.
    retained = {}
    core = {path.resolve() for path in implementation_sources().values()}
    for name, module in list(sys.modules.items()):
        filename = getattr(module, '__file__', None)
        if filename:
            path = Path(filename).resolve()
            if (path in owned or path.is_relative_to(workspace)) and path not in core:
                retained[name] = sys.modules.pop(name)
    original_import = builtins.__import__
    def admitted_import(name, globals=None, locals=None, fromlist=(), level=0):
        # Cached imports bypass meta_path. Check their actual origin as well;
        # ordinary new imports are checked by SourceAdmission before execution.
        cached = sys.modules.get(name) if level == 0 else None
        filename = getattr(cached, '__file__', None)
        if filename and not allowed(Path(filename).resolve()):
            raise ValueError('Unadmitted cached policy/helper import: ' + filename)
        return original_import(name, globals, locals, fromlist, level)
    guard = SourceAdmission()
    previous_bytecode, previous_prefix = sys.dont_write_bytecode, sys.pycache_prefix
    previous_path = list(sys.path)
    sys.dont_write_bytecode = True
    sys.pycache_prefix = str(directory / ('unused-bytecode-' + uuid.uuid4().hex))
    sys.path.insert(0, str(workspace))
    sys.meta_path.insert(0, guard)
    builtins.__import__ = admitted_import
    try:
        yield
        observations.assert_stable()
    except BaseException:
        (directory / 'native-result.json').unlink(missing_ok=True)
        raise
    finally:
        builtins.__import__ = original_import
        sys.meta_path.remove(guard)
        sys.path[:] = previous_path
        sys.dont_write_bytecode, sys.pycache_prefix = previous_bytecode, previous_prefix
        for name, module in list(sys.modules.items()):
            filename = getattr(module, '__file__', None)
            if filename and Path(filename).resolve().is_relative_to(workspace) and Path(filename).resolve() not in core:
                sys.modules.pop(name, None)
        sys.modules.update(retained)


def execute(request_path, *, source_manifest=None, expected_source=None, state=None,
            progress=None, outputs=None, verify_only=False):
    """Execute native-only selected policy; outer worker receipt remains required."""
    parent_manifest = os.environ.get('LEAN_CI_SOURCE_MANIFEST')
    parent_expected = os.environ.get('LEAN_CI_EXPECTED_SOURCE')
    if (source_manifest is not None and parent_manifest is not None
            and Path(source_manifest).resolve() != Path(parent_manifest).resolve()):
        raise ValueError('Explicit SOURCE manifest conflicts with the owned worker boundary')
    if expected_source is not None and parent_expected is not None and expected_source != parent_expected:
        raise ValueError('Explicit expected source conflicts with the owned worker boundary')
    source_manifest = source_manifest or parent_manifest
    expected_source = expected_source or parent_expected
    if source_manifest is None:
        raise ValueError('Frozen execution requires SOURCE.json via argument or LEAN_CI_SOURCE_MANIFEST')
    observations = TemporalInputs()
    manifest_path, manifest, request, adapter, root, package, admitted = admit(
        request_path, source_manifest, expected_source, observations)
    if verify_only and state is None:
        raise ValueError('Receipt-only verification requires the original --state')
    state = Path(state).resolve() if state is not None else Path(tempfile.mkdtemp(prefix='lean-ci-native-')).resolve()
    if state.is_relative_to(root):
        raise ValueError('Native request evidence must stay outside its source root')
    state.mkdir(parents=True, exist_ok=True)
    with locked(state), policy_loading(admitted, Path(manifest['workspace']), observations, state):
        (state / 'native-result.json').unlink(missing_ok=True)
        if request['schema'] == 2:
            from .request import load_request_application
            application = load_request_application(root, package, request, manifest, admitted, observations)
        else:
            spec = importlib.util.spec_from_file_location('_lean_ci_native_' + uuid.uuid4().hex, adapter)
            if spec is None or spec.loader is None:
                raise ValueError('Could not load admitted native policy')
            module = importlib.util.module_from_spec(spec)
            sys.modules[spec.name] = module
            exec(compile(adapter.read_bytes(), str(adapter), 'exec'), module.__dict__)
            factory = getattr(module, 'create_native_application', None)
            mapping = request['coordinates']['source_mapping']
            application = factory(root, package, mapping) if factory else module.create_application(root)
        if (not isinstance(application, Application) or application.root != root
                or application.package_cwd != package):
            raise ValueError('Native factory returned the wrong source/package coordinates')
        runtime = application.runtime
        declared_profile = os.environ.get('R5_LEAN_REMOTE_PROFILE')
        if declared_profile is not None and runtime.environment.get('R5_LEAN_REMOTE_PROFILE') != declared_profile:
            raise ValueError('Native factory dropped or replaced the declared remote profile')
        if declared_profile is not None or 'R5_LEAN_REMOTE_PROFILE' in runtime.environment:
            if ('R5_LEAN_REMOTE_PROFILE' not in runtime.resource_config.names('profile')
                    or resources.remote_profile(runtime.environment, runtime.resource_config) is None):
                raise ValueError('Declared remote profile must be explicitly admitted; local fallback is forbidden')
        progress = application._external(progress or state / 'check-progress')
        outputs = application._external(outputs) if outputs is not None else None
        if outputs is not None:
            outputs.unlink(missing_ok=True)
            outputs.with_suffix(outputs.suffix + '.coverage.json').unlink(missing_ok=True)
        basis = {'kind': 'transport-snapshot', 'content_sha256': expected_source,
                 'workspace': manifest['workspace'], 'source_manifest': str(manifest_path),
                 'source_receipt_sha256': observations.hash_file(manifest_path),
                 'git_head_metadata': manifest.get('git_head')}
        plan = dict(request['payload'], schema=1, invocation=uuid.uuid4().hex,
                    repository=str(root), implementation=request['implementation'],
                    source_files=manifest['files'], source_basis=basis)
        plan['id'] = digest(plan)
        if verify_only:
            path = state / 'native.json'
            if path.is_symlink() or not path.is_file():
                raise ValueError('Receipt-only verification requires the original regular native record')
            record = read_observed(path, observations)
            if (record.get('schema') != 1 or record.get('status') not in ('running', 'completed')
                    or record.get('implementation') != request['implementation']
                    or record.get('request_sha256') != observations.hash_file(Path(request_path).absolute())
                    or record.get('source_basis', {}).get('content_sha256') != expected_source
                    or record.get('source_basis', {}).get('workspace') != manifest['workspace']
                    or not isinstance(record.get('directory'), str)
                    or not isinstance(record.get('toolchain'), dict)):
                raise ValueError('Retained native record differs from the admitted request/source/implementation')
            directory = Path(record['directory']).resolve()
            if not directory.is_relative_to(state / 'runs') or not directory.is_dir():
                raise ValueError('Retained native evidence escaped its invocation')
        else:
            directory = state / 'runs' / ('native-' + plan['invocation'])
            directory.mkdir(parents=True)
        required = application._tasks(plan, 'native', directory)
        if any(task.get('native') is False for task in required):
            raise ValueError('Frozen native requests cannot execute source-only tasks')
        observations.assert_stable()
        toolchain = runtime.compiler_identity(observations.hash_file, cwd=package)
        if verify_only:
            if semantic_toolchain(record['toolchain']) != semantic_toolchain(toolchain):
                raise ValueError('Retained native compiler/runtime differs from current admission')
        else:
            record = {'schema': 1, 'status': 'running', 'source_basis': basis,
                      'request_sha256': observations.hash_file(Path(request_path).absolute()),
                      'implementation': request['implementation'], 'tasks': [],
                      'toolchain': toolchain, 'directory': str(directory)}
            def save(item):
                record['tasks'].append(item)
                write_json(state / 'native.json', record)
            write_json(state / 'native.json', record)
            application.run_tasks(plan, required, directory, progress, toolchain, observations,
                                  observe_toolchain=True, record_task=save)
        reconstructed = application._tasks(plan, 'native', directory)
        if any(task.get('native') is False for task in reconstructed):
            raise ValueError('Frozen native requests cannot verify source-only tasks')
        application.verify_tasks(plan, reconstructed, record['tasks'], toolchain, observations,
                                 observe_toolchain=True)
        if runtime.compiler_identity(observations.hash_file, cwd=package) != toolchain:
            raise ValueError('Native runtime changed during frozen execution')
        observations.assert_stable()
        checks = [item for task, item in zip(required, record['tasks']) if task['kind'] == 'check']
        result = {'schema': 1, 'status': 'succeeded', 'source_basis': basis,
                  'implementation': request['implementation'], 'toolchain': toolchain,
                  'request_sha256': record['request_sha256'], 'selected_payload': request['payload'],
                  'coordinates': request['coordinates'], 'directory': str(state),
                  'source_checks': 'not-executed-by-native-request; local/source coverage remains separate',
                  'outer_receipt_join': {'expected_source': expected_source,
                                         'workspace_phase_ownership': 'outer-worker-receipt-required'},
                  'verification_only': bool(verify_only),
                  'performed_checks': ([] if verify_only else
                      [item['id'] for item in checks if item['result']['mode'] == 'performed']),
                  'reused_checks': [item['id'] for item in checks
                      if verify_only or item['result']['mode'] == 'reused'],
                  'compiled_or_refreshed_targets': ([] if verify_only else sorted({name for item in record['tasks']
                      for name in item['result'].get('compiled_or_refreshed', ())})),
                  'reused_build_targets': sorted({name for item in record['tasks']
                      for name in [*item['result'].get('reused_build_targets', ()),
                                   *(item['result'].get('compiled_or_refreshed', ()) if verify_only else ())]}),
                  'execution_diagnostics': application.execution_diagnostics()}
        if outputs is not None:
            producers = [(task, item['result']) for task, item in zip(required, record['tasks']) if task.get('mapping')]
            result['mapping_groups'] = export_mappings(producers, outputs, toolchain, observations,
                                                       repository_root=root)
            write_json(outputs.with_suffix(outputs.suffix + '.coverage.json'), result)
        application.assert_verified_inputs(observations)
        if verify_only:
            write_json(state / 'native-verification.json',
                       {'status': 'completed', 'original_record_sha256': observations.hash_file(state / 'native.json'),
                        'source_basis': basis, 'toolchain': toolchain,
                        'request_sha256': result['request_sha256']})
        else:
            record.update(status='completed', toolchain=toolchain)
            write_json(state / 'native.json', record)
        write_json(state / 'native-result.json', result)
        return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request', type=Path)
    parser.add_argument('--source-manifest', type=Path)
    parser.add_argument('--expected-source')
    parser.add_argument('--state', type=Path)
    parser.add_argument('--progress', type=Path)
    parser.add_argument('--outputs', type=Path)
    parser.add_argument('--verify-only', action='store_true',
                        help='reconstruct retained native receipts without executing tasks; requires original --state')
    args = parser.parse_args(argv)
    try:
        print(json.dumps(execute(args.request, source_manifest=args.source_manifest,
                                 expected_source=args.expected_source, state=args.state,
                                 progress=args.progress, outputs=args.outputs, verify_only=args.verify_only), indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError) as error:
        print('Frozen native execution failed closed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
