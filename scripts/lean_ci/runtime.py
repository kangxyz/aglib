"""Guarded native execution and actual compiler/runtime identities."""
from dataclasses import asdict
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess

from . import resources
from .state import InputDrift, file_hash, read_json, valid_receipt


def managed_mechanism(profile, physical_lean, hash_file):
    """Recognize the content-addressed worker wrapper, otherwise keep strict keys.

    Only invocation coordinates in the known compiler configuration are erased.
    Actual wrapper/config/producer bytes stay in the invocation's source guard.
    """
    try:
        wrapper = Path(profile['lean'])
        hash_file(wrapper)
        text = wrapper.read_text()
        lines = text.splitlines()
        if len(lines) != 2 or lines[0] != '#!/bin/sh':
            return None
        args = shlex.split(lines[1])
        if len(args) != 6 or args[0] != 'exec' or args[3] != '__compiler__' or args[5] != '$@':
            return None
        python, worker, config_path = map(Path, (args[1], args[2], args[4]))
        run = wrapper.parents[2]
        if (not python.is_absolute() or not worker.is_absolute()
                or config_path != run / 'compiler-config.json'
                or text != '#!/bin/sh\nexec ' + shlex.join(args[1:5]) + ' "$@"\n'):
            return None
        expected = re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*-([0-9a-f]{64})\.py', worker.name)
        if expected is None or hash_file(worker) != expected[1]:
            return None
        tree = ast.parse(worker.read_text())
        sidecar = next((node.value.value for node in tree.body
            if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name)
                and target.id == 'ELASTIC_MODULE' for target in node.targets)
            and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str)), None)
        sidecar_name = re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*-([0-9a-f]{64})\.py', sidecar or '')
        if sidecar_name is None or hash_file(worker.with_name(sidecar)) != sidecar_name[1]:
            return None
        hash_file(config_path)
        config = read_json(config_path)
        hash_file(config_path)
        if (Path(config['lean']).resolve() != Path(physical_lean).resolve()
                or any(config[name] != profile[key] for name, key in
                       [('jobs', 'jobs'), ('threads', 'threads'), ('heap_mib', 'lean_memory_mib')])
                or config['slots'] != str(run / 'slots')
                or config['events'] != str(run / 'compiler-events.jsonl')):
            return None
        stable = dict(config, slots='<run>/slots', events='<run>/compiler-events.jsonl')
        for field in ('scope_fds', 'scope_leases'):
            if field in stable:
                stable[field] = {'count': len(stable[field])}
        if stable.get('scope_supervisor') is not None:
            owner = dict(stable['scope_supervisor'])
            if owner.get('run_dir') != str(run):
                return None
            owner.update(pid='<supervisor>', start='<process-start>', run_dir='<run>')
            stable['scope_supervisor'] = owner
        if stable.get('elastic') is not None:
            elastic = dict(stable['elastic'])
            if elastic.get('run_dir') != str(run):
                return None
            elastic['run_dir'] = '<run>'
            stable['elastic'] = elastic
        template = '#!/bin/sh\nexec ' + shlex.join([str(python), str(worker), '__compiler__', '<config>']) + ' "$@"\n'
        return {'wrapper_template': hashlib.sha256(template.encode()).hexdigest(),
                'worker': str(worker), 'worker_sha256': expected[1],
                'sidecar_sha256': sidecar_name[1], 'python': str(python.resolve()),
                'python_sha256': hash_file(python), 'configuration': stable}
    except InputDrift:
        raise
    except (OSError, ValueError, KeyError, TypeError, IndexError, SyntaxError):
        return None


def semantic_environment(environment, toolchain):
    """Normalize only the admitted managed overlay; retain other path/options."""
    value = dict(environment)
    profile = (toolchain or {}).get('managed_profile')
    if not profile or not toolchain.get('managed_mechanism'):
        return value
    wrapper = profile['lean']
    overlay = str(Path(wrapper).parent.parent)
    for key in ('LEAN', 'LAKE_OVERRIDE_LEAN'):
        if value.get(key) == wrapper:
            value[key] = '<managed-lean>'
    if value.get('LEAN_SYSROOT') == overlay:
        value['LEAN_SYSROOT'] = '<managed-sysroot>'
    if value.get('PATH'):
        value['PATH'] = ':'.join('<managed-bin>' if p == str(Path(wrapper).parent) else p
                                 for p in value['PATH'].split(':'))
    config = toolchain.get('resource_configuration', {})
    names = [config.get('prefix', 'LEAN_CI') + '_REMOTE_PROFILE', *config.get('profile_keys', ())]
    stable = {key: item for key, item in profile.items() if key != 'lean'}
    for key in names:
        if value.get(key) is not None:
            value[key] = json.dumps(stable, sort_keys=True, separators=(',', ':'))
    return value


def semantic_toolchain(toolchain, *, installation=False):
    """Cache identity; full actual identity still guards each live invocation."""
    value = dict(toolchain or {})
    if not installation:
        value.pop('installation', None)
    if value.get('managed_profile') and value.get('managed_mechanism'):
        value.pop('managed_wrapper', None)
        value['execution_environment'] = semantic_environment(value.get('execution_environment', {}), toolchain)
        value['managed_profile'] = {key: item for key, item in value['managed_profile'].items() if key != 'lean'}
        value['managed_wrapper_boundary'] = 'observed-outer-worker-profile-v1'
    return value


def compiler_identity(root, hash_file=file_hash, *, environment=None, resource_config=None):
    """Observe executable and shared-runtime inputs before any check-cache lookup."""
    environment = dict(os.environ if environment is None else environment)
    if 'LEAN_GITHASH' in environment:
        raise ValueError('LEAN_GITHASH overrides are unsupported for production CI identity')
    config = resource_config or resources.ResourceConfig()
    profile = resources.remote_profile(environment, config)
    observer = getattr(hash_file, '__self__', None)
    if profile:
        # Managed wrappers are explicitly parent-approved. Resolve the physical
        # library behind an overlay, and bind both wrapper and physical runtime.
        library = Path(environment['LEAN_SYSROOT']) / 'lib/lean'
        if not library.is_dir():
            raise ValueError('Unsupported managed runtime: no physical lib/lean provenance')
        installation = library.resolve().parent.parent
        paths = {name: installation / 'bin' / name for name in ('lean', 'lake')}
        if not all(path.is_file() for path in paths.values()):
            raise ValueError('Unsupported managed runtime: physical lean/lake provenance is missing')
        result = {'managed_wrapper': hash_file(Path(profile['lean'])), 'managed_profile': profile}
        mechanism = managed_mechanism(profile, paths['lean'], hash_file)
        if mechanism is not None:
            result['managed_mechanism'] = mechanism
    else:
        paths = {tool: Path(subprocess.check_output(['elan', 'which', tool], cwd=root,
                                                    text=True, env=environment).strip())
                 for tool in ('lean', 'lake')}
        installation = paths['lean'].resolve().parent.parent
        library = paths['lean'].parent.parent / 'lib/lean'
        result = {}
    result.update({name: hash_file(path) for name, path in paths.items()})
    result['installation'] = str(installation)
    if observer is not None and hasattr(observer, 'observe_resolution'):
        observer.observe_resolution(library)
    for pattern in ('libleanshared*', 'libLake_shared*'):
        for shared in sorted(library.glob(pattern)):
            if shared.is_file():
                result[shared.name] = hash_file(shared)
    names = {'PATH', 'ELAN_TOOLCHAIN', 'LEAN_OPTIONS', 'LEAN_OPTS', 'LEAN_ARGS',
             'LAKE_ARGS', 'LEAN_PATH', 'LEAN', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN'}
    if profile is not None:
        names.update(('PYTHONPATH', 'PYTHONHOME'))
    names.update(key for kind in ('profile', 'memory', 'rss', 'build_thread') for key in config.names(kind))
    result['execution_environment'] = {name: environment.get(name) for name in sorted(names)}
    result['resource_configuration'] = {key: list(value) if isinstance(value, tuple) else value
                                        for key, value in asdict(config).items()}
    return result


def command_matches(logical, actual):
    logical, actual = list(logical), list(actual)
    if logical[:1] == ['lean'] and len(actual) == len(logical):
        if Path(actual[0]).name != 'lean':
            return False
        actual[0] = 'lean'
    if logical[:3] == ['lake', 'env', 'lean'] and len(actual) == len(logical):
        if Path(actual[2]).name != 'lean':
            return False
        actual[2] = 'lean'
    return actual == logical


class NativeRuntime:
    def __init__(self, root, resource_config=None, environment=None):
        self.root = Path(root).resolve()
        self.resource_config = resource_config or resources.ResourceConfig()
        self.environment = dict(os.environ if environment is None else environment)

    def compiler_identity(self, hash_file=file_hash, *, cwd=None):
        return compiler_identity(self.root if cwd is None else Path(cwd), hash_file,
                                 environment=self.environment,
                                 resource_config=self.resource_config)

    def run(self, task, directory):
        """Run one direct command in the caller's already prepared environment."""
        if task['kind'] != 'process':
            raise ValueError('Native runtime accepts direct process commands only')
        directory.mkdir(parents=True, exist_ok=True)
        cwd, command = Path(task['cwd']), task['command']
        receipt_path = directory / 'resource.json'
        with receipt_path.open('x') as reserved:
            json.dump({'state': 'reserved'}, reserved)
        code = resources.run(command, cwd=cwd, env=self.environment,
                             receipt=receipt_path,
                             budget=resources.limits(self.environment, config=self.resource_config),
                             config=self.resource_config)
        receipt = read_json(receipt_path)
        if code or not valid_receipt(receipt, cwd=cwd) or not command_matches(command, receipt['command']):
            raise ValueError(f'Native command failed: {task["id"]}')
        return {'receipt': receipt}
