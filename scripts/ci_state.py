"""Trusted-producer CI check progress, separate from Lake compilation evidence.

Callers must validate the native graph with Lake --rehash before consuming
module identities. These records do not authorize skipping a graph validation.
They are compatibility records, not adversarially authenticated certificates.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import uuid

from library_sources import MODULE, module_path


SCHEMA = 1


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    try:
        temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def valid_receipt(receipt, command=None, cwd=None):
    if not isinstance(receipt, dict):
        return False
    return (receipt.get('state') == 'completed' and type(receipt.get('exit_code')) is int
            and receipt['exit_code'] == 0 and receipt.get('guard_failure', 'missing') is None
            and receipt.get('owned_group_gone') is True
            and isinstance(receipt.get('command'), list) and bool(receipt['command'])
            and (command is None or receipt['command'] == list(map(str, command)))
            and (cwd is None or receipt.get('cwd') == str(cwd)))


def module_identity(root, name, hash_file=file_hash):
    """Consume native traces, never reconstruct Lake's transitive build hash."""
    root = Path(root)
    relative = module_path(name).with_suffix('')
    trace_path = root / '.lake/build/lib/lean' / relative.with_suffix('.trace')
    hash_file(trace_path)
    trace = read_json(trace_path)
    hash_file(trace_path)
    if (trace.get('schemaVersion') != '2025-09-10'
            or not isinstance(trace.get('depHash'), str)
            or not re.fullmatch('[0-9a-f]{16}', trace['depHash'])
            or not isinstance(trace.get('outputs'), dict)):
        raise ValueError('Unsupported native trace: ' + str(trace_path))
    outputs = {}
    expected = trace['outputs']
    if type(expected.get('m')) is not bool:
        raise ValueError('Missing native module-system output discriminator: ' + name)
    facets = {'o': ['.olean'], 'i': ['.ilean'], 'c': ['.c']}
    if expected['m']:
        facets.update(o=['.olean', '.olean.server', '.olean.private'], r=['.ir'], rs=['.ir.sig'])
    # Artifact names in traces are content hashes, not paths or module names.
    for facet, suffixes in facets.items():
        recorded = expected.get(facet)
        names = recorded if isinstance(recorded, list) else [recorded]
        if len(names) != len(suffixes) or any(not isinstance(n, str) or
                not re.fullmatch('[0-9a-f]{16}' + re.escape(suffix), n)
                for n, suffix in zip(names, suffixes)):
            raise ValueError(f'Missing/unsupported {facet} output in native trace: {name}')
        for suffix in suffixes:
            folder = '.lake/build/ir' if suffix == '.c' else '.lake/build/lib/lean'
            output = root / folder / Path(str(relative) + suffix)
            outputs[output.relative_to(root).as_posix()] = hash_file(output)
    return {'depHash': trace['depHash'], 'outputs': outputs}


def locate_module(root, name):
    """Locate one explicit checker-runtime module without asking Lake per module."""
    relative = module_path(name)
    if (root / relative).is_file():
        return root
    packages = root / '.lake/packages'
    matches = [p for p in packages.iterdir() if (p / relative).is_file()] if packages.is_dir() else []
    if len(matches) != 1:
        raise ValueError('Missing/ambiguous checker-runtime module: ' + name)
    return matches[0]


def check_binding(root, kind, modules, arguments, policy_paths, runtime_modules=(),
                  raw_paths=(), toolchain=None, generated=None, hash_file=file_hash):
    root = Path(root)
    paths = sorted(set(map(str, [*policy_paths, *raw_paths])))
    raw = {path: hash_file(root / path) if (root / path).is_file() else None for path in paths}
    native = {name: module_identity(root, name, hash_file) for name in sorted(set(modules))}
    runtime = {}
    for name in sorted(set(runtime_modules)):
        owner = locate_module(root, name)
        runtime[name] = {'source': hash_file(owner / module_path(name)),
                         'native': module_identity(owner, name, hash_file)}
    return {'schema': SCHEMA, 'kind': kind, 'modules': sorted(set(modules)),
            'arguments': list(arguments), 'raw_inputs': raw, 'native': native,
            'checker_runtime': runtime, 'toolchain': toolchain,
            'generated_source': generated,
            # Native depHash intentionally omits some weak arguments.
            'environment': {key: os.environ.get(key) for key in
                            ('ELAN_TOOLCHAIN', 'LEAN_OPTIONS', 'LEAN_OPTS', 'LEAN_ARGS',
                             'LAKE_ARGS', 'LEAN_PATH', 'LEAN', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN')}}


class InputDrift(ValueError):
    """A temporal input changed inside this check attempt."""


class ReflectionUnavailable(ValueError):
    """No complete standard-Lake reflection boundary can be certified."""


class ReflectionGraph:
    """One phase's native import/artifact snapshot with per-root closure keys.

    Pinned .ilean v5 records every EXPLICIT parsed header import. Follow all
    flags, including private and meta branches. Standard Lake compilation is
    required; custom ModuleSetup.imports overrides are outside this interface.
    Implicit Init is resolved through the actual ordered search path too.
    """
    def __init__(self, root, search_path, toolchain):
        self.root = Path(root).absolute()
        self.toolchain = toolchain
        installation = toolchain.get('installation')
        if not isinstance(installation, str) or not Path(installation).is_absolute():
            raise ReflectionUnavailable('Missing resolved compiler installation provenance')
        self.installation = Path(installation).resolve()
        self.search_path = [Path(p).absolute() for p in search_path]
        if any(not Path(p).is_absolute() for p in search_path):
            raise ReflectionUnavailable('Nonabsolute native import search path')
        compiler_path = self.installation / 'lib/lean'
        if compiler_path not in self.search_path:
            self.search_path.append(compiler_path)
        self.files, self.nodes, self.failures, self.missing = {}, {}, {}, set()
        self.hash_count = 0

    @staticmethod
    def stamp(path):
        value = path.stat()
        return (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns)

    def hash_file(self, path):
        path = Path(path).absolute()
        if path in self.missing:
            raise InputDrift('Previously absent reflective input appeared: ' + str(path))
        stamp = self.stamp(path)
        if path in self.files:
            old_stamp, value = self.files[path]
            if old_stamp != stamp:
                raise InputDrift('Reflective input changed during this attempt: ' + str(path))
            return value
        value = file_hash(path)
        if self.stamp(path) != stamp:
            raise InputDrift('Reflective input changed while hashing: ' + str(path))
        self.files[path] = (stamp, value)
        self.hash_count += 1
        return value

    def assert_stable(self):
        for path, (stamp, _) in self.files.items():
            if self.stamp(path) != stamp:
                raise InputDrift('Reflective input changed during this attempt: ' + str(path))
        for path in self.missing:
            if path.exists():
                raise InputDrift('Previously absent reflective input appeared: ' + str(path))

    def optional_hash(self, path):
        path = Path(path).absolute()
        if path.is_file():
            return self.hash_file(path)
        if path in self.files:
            raise InputDrift('Reflective input disappeared: ' + str(path))
        self.missing.add(path)
        return None

    def node(self, name):
        if name in self.failures:
            raise ReflectionUnavailable(self.failures[name])
        if name in self.nodes:
            return self.nodes[name]
        try:
            if not isinstance(name, str) or MODULE.fullmatch(name) is None:
                raise ReflectionUnavailable('Malformed native import name')
            relative = module_path(name).with_suffix('')
            library = next((p for p in self.search_path if (p / (str(relative) + '.olean')).is_file()), None)
            if library is None:
                raise ReflectionUnavailable('Unresolved native import: ' + name)
            metadata_path = library / (str(relative) + '.ilean')
            metadata_hash = self.hash_file(metadata_path)
            metadata = read_json(metadata_path)
            self.hash_file(metadata_path)  # Parsing must observe the same file.
            if (not isinstance(metadata, dict) or type(metadata.get('version')) is not int
                    or metadata['version'] != 5 or metadata.get('module') != name
                    or not isinstance(metadata.get('directImports'), list)):
                raise ReflectionUnavailable('Unsupported/wrong-module native import metadata: ' + name)
            imports = metadata['directImports']
            if any(not isinstance(row, list) or len(row) != 4
                   or not isinstance(row[0], str) or MODULE.fullmatch(row[0]) is None
                   or any(type(flag) is not bool for flag in row[1:]) for row in imports):
                raise ReflectionUnavailable('Malformed native import metadata: ' + name)
            if library.resolve() == (self.installation / 'lib/lean').resolve():
                # Installation provenance, not a Lean/Init namespace shortcut.
                artifacts = {suffix: self.optional_hash(library / (str(relative) + suffix))
                             for suffix in ('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.ir.sig')
                             }
                native = {'installation': {k: v for k, v in self.toolchain.items() if k != 'installation'},
                          'artifacts': artifacts}
                owner = 'compiler-installation'
                source = next((p for p in (self.installation / 'src/lean' / module_path(name),
                                           self.installation / 'src/lean/lake' / module_path(name)) if p.is_file()), None)
            else:
                if library.parts[-4:] != ('.lake', 'build', 'lib', 'lean'):
                    raise ReflectionUnavailable('Unknown noncompiler import provenance: ' + name)
                package = library.parents[3]
                native = module_identity(package, name, self.hash_file)
                owner = ('workspace:' + str(library.relative_to(self.root)) if library.is_relative_to(self.root)
                         else 'external:' + str(library.resolve()))
                source = package / module_path(name)
                if not source.is_file():
                    raise ReflectionUnavailable('Missing native import source provenance: ' + name)
            value = {'owner': owner, 'native': native, 'metadata': metadata_hash,
                     'source': self.hash_file(source) if source else None,
                     'imports': sorted(set(row[0] for row in imports))}
            self.nodes[name] = value
            return value
        except InputDrift:
            raise
        except (OSError, ValueError, TypeError) as error:
            self.failures[name] = str(error)
            raise ReflectionUnavailable(str(error)) from error

    def closure(self, roots):
        try:
            self.assert_stable()
            roots = sorted(set([*roots, 'Init']))
            pending, seen = list(roots), set()
            while pending:
                name = pending.pop()
                if name in seen:
                    continue
                seen.add(name)
                pending.extend(self.node(name)['imports'])
            self.assert_stable()
            return {'schema': 1, 'roots': roots,
                    'digest': digest({name: self.nodes[name] for name in sorted(seen)})}
        except ReflectionUnavailable:
            # Unsupported metadata is a check-cache miss, never a build waiver.
            return None


def valid_success(record, binding):
    return (isinstance(record, dict) and record.get('schema') == SCHEMA
            and record.get('status') == 'success' and record.get('binding') == binding
            and record.get('key') == digest(binding)
            and valid_receipt(record.get('receipt'), record.get('executed_command'))
            and isinstance(record.get('executed_command'), list)
            and record.get('logical_arguments') == binding['arguments']
            and arguments_match(binding['arguments'], record['executed_command']))


def arguments_match(expected, actual):
    actual = list(actual)
    if expected[:3] == ['lake', 'env', 'lean'] and len(actual) == len(expected):
        if Path(actual[2]).name != 'lean':
            return False
        actual[2] = 'lean'
    if expected and expected[-1] == '<selected-origin-audit>' and len(actual) == len(expected):
        if not str(actual[-1]).endswith('.lean'):
            return False
        actual[-1] = expected[-1]
    return actual == expected


class Progress:
    def __init__(self, directory):
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=True)

    def lookup(self, binding):
        try:
            record = read_json(self.directory / (digest(binding) + '.json'))
            return record if valid_success(record, binding) else None
        except (OSError, ValueError, TypeError):
            return None

    def save(self, binding, receipt, executed_command):
        if not valid_receipt(receipt, executed_command):
            raise ValueError('A check success requires an exit-zero, closed-group resource receipt')
        record = {'schema': SCHEMA, 'key': digest(binding), 'status': 'success',
                  'binding': binding, 'logical_arguments': binding['arguments'],
                  'executed_command': list(map(str, executed_command)), 'receipt': receipt}
        if not valid_success(record, binding):
            raise ValueError('Check receipt does not match its actual required arguments')
        write_json(self.directory / (record['key'] + '.json'), record)
        return record

    def run(self, binding_function, execute, reuse=True):
        """Only compatible successes reuse; failed/stale/partial inputs rerun."""
        before = binding_function()
        record = self.lookup(before) if reuse else None
        if record is not None:
            # Even a lookup is bounded by the same before/after input check.
            if binding_function() != before:
                raise ValueError('Check inputs drifted while reading reusable success')
            return {'mode': 'reused', 'success': record}
        receipt, command = execute()
        if binding_function() != before:
            raise ValueError('Check inputs drifted during execution; success was not recorded')
        record = self.save(before, receipt, command)
        return {'mode': 'performed', 'success': record}
