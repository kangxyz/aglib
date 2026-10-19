"""Guarded native execution and actual compiler/runtime identities."""
from dataclasses import asdict
import os
from pathlib import Path
import subprocess

from . import build, resources
from .source import module_path
from .state import ReflectionGraph, file_hash, module_identity, read_json, valid_receipt


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
        directory.mkdir(parents=True, exist_ok=True)
        cwd, command = Path(task['cwd']), task['command']
        generated_stamp = None
        generated_path = None
        if task.get('generated'):
            index = task.get('generated_argument_index', -1)
            generated_path = Path(task.get('generated_path', command[index]))
            if not generated_path.is_absolute():
                generated_path = cwd / generated_path
            argument_path = Path(command[index])
            if not argument_path.is_absolute():
                argument_path = cwd / argument_path
            if argument_path.resolve() != generated_path.resolve():
                raise ValueError('Generated input path does not match its actual command argument')
            generated_path.parent.mkdir(parents=True, exist_ok=True)
            generated_path.write_text(task['generated'])
            generated_stamp = ReflectionGraph.stamp(generated_path)
        if task['kind'] == 'build':
            before = {n: self.trace_stamp(cwd, n) for n in task['modules']}
            selection = task.get('build_selection', 'library')
            selectors = build.native_targets(task['modules'], selection)
            mapping = Path(task['mapping']) if task.get('mapping') else None
            expected = ['lake', '--rehash', 'build', *selectors]
            if mapping is not None:
                expected += ['-o', str(mapping.resolve())]
            if command != expected:
                raise ValueError('Build task command disagrees with semantic targets/selection')
            code = build.build(cwd, task['modules'], directory, rehash=True, outputs=mapping,
                               environment=self.environment, config=self.resource_config, selection=selection)
            if code:
                raise ValueError(f'Selected build failed ({code}): {task["id"]}')
            cached = read_json(directory / 'cached-check.json')
            if valid_receipt(cached, expected[:2] + ['--no-build'] + expected[2:], cwd):
                receipt, performed = cached, False
            else:
                if (cached.get('exit_code') != 3 or cached.get('guard_failure', 'missing') is not None
                        or cached.get('owned_group_gone') is not True
                        or not build.expected_cache_miss(3, (directory / 'cached-check.log').read_text())):
                    raise ValueError('Selected build has no valid cache-miss evidence')
                receipt, performed = read_json(directory / 'graph-build.json'), True
                if not valid_receipt(receipt, command, cwd):
                    raise ValueError('Selected build has no successful guarded native graph receipt')
            compiled = [n for n in task['modules'] if performed and self.trace_stamp(cwd, n) != before[n]]
            result = {'receipt': receipt, 'compiled_or_refreshed': compiled,
                      'reused_build_targets': [] if performed else task['modules']}
            return self._outputs(task, result)
        before = {n: self.trace_stamp(cwd, n) for n in task.get('modules', [])}
        budget = resources.limits(self.environment, config=self.resource_config)
        receipt_path = directory / 'resource.json'
        if task['kind'] == 'environment':
            with Path(task['environment_output']).open('w') as output:
                code = resources.run(command, cwd=cwd, receipt=receipt_path, budget=budget, stdout=output, env=self.environment, config=self.resource_config)
        elif task.get('capped'):
            threads = build.build_threads(self.environment, self.resource_config)
            budget['native_build_threads'] = threads
            with build.capped_toolchain(cwd, threads=threads, environment=self.environment, config=self.resource_config) as env:
                bounded = resources.capped_command(command, env, self.resource_config)
                code = resources.run(bounded, cwd=cwd, env=env, receipt=receipt_path, budget=budget, config=self.resource_config)
        else:
            code = resources.run(command, cwd=cwd, env=self.environment, receipt=receipt_path, budget=budget, config=self.resource_config)
        receipt = read_json(receipt_path)
        if generated_path is not None and (generated_path.read_text() != task['generated']
                                           or ReflectionGraph.stamp(generated_path) != generated_stamp):
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
        return self._outputs(task, result)

    def _outputs(self, task, result):
        cwd = Path(task['cwd'])
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


def parse_search_path(output):
    paths = output.strip().split(os.pathsep) if output.strip() else []
    if any(not Path(p).is_absolute() for p in paths):
        raise ValueError('Unknown/nonabsolute resolved Lake import search path')
    return paths


# Kept as a descriptive compatibility name for small adapters.
Executor = NativeRuntime
