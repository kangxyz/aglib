"""Trusted-producer CI check progress, separate from Lake compilation evidence.

Callers must validate the native graph with Lake --rehash before consuming
module identities. These records do not authorize skipping a graph validation.
They are compatibility records, not adversarially authenticated certificates.
"""
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import time
import uuid

from .source import IDENT, MODULE, module_path


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
    context = getattr(hash_file, '__self__', None)
    stable = getattr(context, 'assert_stable', None)
    if callable(stable):
        stable()
    observer = getattr(context, 'optional_hash', None)
    # Propagate the phase snapshot's absence observations as well as its hashes.
    # The content key stays None for an absent optional input across runs.
    raw = {path: (observer(root / path) if callable(observer) else
                  hash_file(root / path) if (root / path).is_file() else None) for path in paths}
    native_hash = getattr(context, 'native_hash_file', hash_file)
    native = {name: module_identity(root, name, native_hash) for name in sorted(set(modules))}
    runtime = {}
    for name in sorted(set(runtime_modules)):
        owner = locate_module(root, name)
        runtime[name] = {'source': hash_file(owner / module_path(name)),
                         'native': module_identity(owner, name, native_hash)}
    value = {'schema': SCHEMA, 'kind': kind, 'modules': sorted(set(modules)),
            'arguments': list(arguments), 'raw_inputs': raw, 'native': native,
            'checker_runtime': runtime, 'toolchain': toolchain,
            'generated_source': generated,
            # Native depHash intentionally omits some weak arguments.
            'environment': {key: os.environ.get(key) for key in
                            ('ELAN_TOOLCHAIN', 'LEAN_OPTIONS', 'LEAN_OPTS', 'LEAN_ARGS',
                             'LAKE_ARGS', 'LEAN_PATH', 'LEAN', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN')}}
    if callable(stable):
        stable()
    return value


class InputDrift(ValueError):
    """A temporal input changed inside this check attempt."""


class ReflectionUnavailable(ValueError):
    """No complete standard-Lake reflection boundary can be certified."""


class TemporalInputs:
    """One guard lifetime's content hashes and temporal filesystem observations.

    Temporal stamps never enter compatibility keys. Ordinary present-file
    parents retain no directory timestamps; absent names require their nearest
    existing parent's timestamp to detect transient creation/removal.
    """
    def __init__(self, *, hash_cache=None):
        self.hash_cache = hash_cache if hash_cache is not None else {}
        self._inspection_depth = 0
        self.scan_count, self.scan_seconds = 0, 0.0
        self.files, self.missing, self.components = {}, set(), {}
        self.resolution = {}
        self.hash_count = 0
        self.directories = {}

    @staticmethod
    def stat_identity(value):
        return (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns,
                value.st_ctime_ns, value.st_mode)

    @classmethod
    def stamp(cls, path):
        return cls.stat_identity(path.stat())

    @classmethod
    def path_state(cls, path):
        """Observe both a lookup result and its symlink/directory-entry identity."""
        def sample(follow):
            try:
                return cls.stat_identity(path.stat() if follow else path.lstat())
            except (FileNotFoundError, NotADirectoryError):
                return None
        before = sample(False)
        followed = sample(True)
        if sample(False) != before:
            raise InputDrift('Import resolution changed while observing: ' + str(path))
        return followed, before

    @classmethod
    def component_state(cls, path):
        try:
            value = path.lstat()
        except (FileNotFoundError, NotADirectoryError):
            return None
        if stat.S_ISLNK(value.st_mode):
            return ('symlink', cls.stat_identity(value), os.readlink(path))
        # Normal cache writes can change a parent directory's timestamp without
        # changing how it resolves a present input. Keep its identity, not times.
        return ('entry', value.st_dev, value.st_ino, stat.S_IFMT(value.st_mode))

    def observe_components(self, path):
        for component in [*reversed(path.parents), path]:
            state = self.component_state(component)
            if component in self.components and self.components[component] != state:
                raise InputDrift('Input path component changed during this attempt: ' + str(component))
            if state is not None:
                self.components[component] = state

    def observe_resolution(self, path):
        path = Path(path).absolute()
        self.observe_components(path)
        def observe(candidate):
            state = self.path_state(candidate)
            if candidate in self.resolution and self.resolution[candidate] != state:
                raise InputDrift('Import resolution changed during this attempt: ' + str(candidate))
            self.resolution[candidate] = state
            return state
        state = observe(path)
        # An absent name can appear and disappear without leaving a leaf stat.
        # Its nearest existing parent records that directory-entry mutation.
        if state[0] is None:
            parent = path.parent
            while True:
                parent_state = observe(parent)
                if parent_state[0] is not None or parent == parent.parent:
                    break
                parent = parent.parent
        return state

    def observe_directory(self, path, excluded=()):
        """Watch source enrollment names, excluding explicit ignored setup entries.

        File bytes and absent/shadow candidates are separately observed. Unlike
        an absent candidate guard, this inventory does not certify transient
        create/remove events for names absent at both observations.
        """
        path = Path(path).absolute()
        self.observe_components(path)
        excluded = tuple(sorted(set(excluded)))
        if any('/' in name or name in ('', '.', '..') for name in excluded):
            raise ValueError('Directory exclusions must be immediate entry names')
        value = self.directory_state(path, excluded)
        key = (path, excluded)
        if key in self.directories and self.directories[key] != value:
            raise InputDrift('Source enrollment directory changed: ' + str(path))
        self.directories[key] = value
        return value

    @classmethod
    def directory_state(cls, path, excluded):
        return (cls.component_state(path), sorted(
            (entry.name, stat.S_IFMT(entry.lstat().st_mode)) for entry in path.iterdir()
            if entry.name not in excluded))

    def hash_file(self, path):
        path = Path(path).absolute()
        self.observe_components(path)
        if path in self.missing:
            raise InputDrift('Previously absent reflective input appeared: ' + str(path))
        stamp = self.stamp(path)
        if path in self.files:
            old_stamp, value = self.files[path]
            if old_stamp != stamp:
                raise InputDrift('Reflective input changed during this attempt: ' + str(path))
            return value
        cached = self.hash_cache.get(path)
        if cached is not None and cached[0] == stamp:
            value = cached[1]
        else:
            value = file_hash(path)
            self.hash_count += 1
        if self.stamp(path) != stamp:
            raise InputDrift('Reflective input changed while hashing: ' + str(path))
        self.files[path] = (stamp, value)
        self.hash_cache[path] = (stamp, value)
        return value

    @contextmanager
    def inspection(self):
        """Coalesce pure binding scans; never enclose execution or external use.

        Each file access still checks its own stamp. The outer exit checks all
        observations before a computed binding can escape to its consumer.
        """
        outer = self._inspection_depth == 0
        if outer:
            self.assert_stable()
        self._inspection_depth += 1
        try:
            yield self
        finally:
            self._inspection_depth -= 1
            if outer:
                self.assert_stable()

    def assert_stable(self):
        if self._inspection_depth:
            return
        started = time.perf_counter()
        self.scan_count += 1
        try:
            self._scan_stable()
        finally:
            self.scan_seconds += time.perf_counter() - started

    def _scan_stable(self):
        for (path, excluded), value in self.directories.items():
            if self.directory_state(path, excluded) != value:
                raise InputDrift('Source enrollment directory changed: ' + str(path))
        for path, (stamp, _) in self.files.items():
            if self.stamp(path) != stamp:
                raise InputDrift('Reflective input changed during this attempt: ' + str(path))
        for path in self.missing:
            if path.exists():
                raise InputDrift('Previously absent reflective input appeared: ' + str(path))
        for path, state in self.resolution.items():
            if self.path_state(path) != state:
                raise InputDrift('Import resolution changed during this attempt: ' + str(path))
        for path, state in self.components.items():
            if self.component_state(path) != state:
                raise InputDrift('Input path component changed during this attempt: ' + str(path))

    def optional_hash(self, path):
        path = Path(path).absolute()
        if path.is_file():
            return self.hash_file(path)
        self.observe_resolution(path)
        if path.exists():
            raise ReflectionUnavailable('Expected a regular reflective input file: ' + str(path))
        if path in self.files:
            raise InputDrift('Reflective input disappeared: ' + str(path))
        self.missing.add(path)
        return None


class CheckInputs:
    """Whole-attempt sources plus one consuming interval's native observations.

    Create a fresh instance for each check and for final aggregate verification.
    Shared hash/metadata caches are content-work optimizations, not observations.
    """
    def __init__(self, whole, *, hash_cache=None, metadata_cache=None):
        self.whole = whole
        self.native = TemporalInputs(hash_cache=hash_cache)
        self.metadata_cache = metadata_cache if metadata_cache is not None else {}

    @property
    def hash_count(self):
        return self.whole.hash_count + self.native.hash_count

    @property
    def scan_count(self):
        return self.whole.scan_count + self.native.scan_count

    @property
    def scan_seconds(self):
        return self.whole.scan_seconds + self.native.scan_seconds

    def hash_file(self, path):
        return self.whole.hash_file(path)

    def optional_hash(self, path):
        return self.whole.optional_hash(path)

    def native_hash_file(self, path):
        return self.native.hash_file(path)

    def native_optional_hash(self, path):
        return self.native.optional_hash(path)

    def observe_resolution(self, path):
        return self.native.observe_resolution(path)

    def observe_directory(self, path, excluded=()):
        return self.whole.observe_directory(path, excluded)

    def assert_stable(self):
        self.whole.assert_stable()
        self.native.assert_stable()

    @contextmanager
    def inspection(self):
        with self.whole.inspection(), self.native.inspection():
            yield self


class ReflectionGraph:
    """Standard-Lake .ilean v5 import closure with scoped native observations.

    Follow all explicit imports, regardless of flags. Custom ModuleSetup.imports
    overrides are outside this interface. Resolve implicit Init on the same
    actual search path, without a namespace-based compiler shortcut.
    """
    stat_identity = staticmethod(TemporalInputs.stat_identity)
    stamp = staticmethod(TemporalInputs.stamp)

    def __init__(self, root, search_path, toolchain, observations=None):
        self.observations = observations if observations is not None else TemporalInputs()
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
        self.nodes, self.failures = {}, {}

    @property
    def hash_count(self):
        return self.observations.hash_count

    def hash_file(self, path):
        hasher = getattr(self.observations, 'native_hash_file', self.observations.hash_file)
        return hasher(path)

    def optional_hash(self, path):
        hasher = getattr(self.observations, 'native_optional_hash', self.observations.optional_hash)
        return hasher(path)

    def assert_stable(self):
        self.observations.assert_stable()

    def resolve_library(self, name):
        # Lean SearchPath.findWithExt chooses the first namespace root, even
        # when that entry has no artifact for this particular child module.
        root = re.match(IDENT, name).group()
        root = root[1:-1] if root.startswith('«') else root
        for library in self.search_path:
            namespace, _ = self.observations.observe_resolution(library / root)
            artifact, _ = self.observations.observe_resolution(library / (root + '.olean'))
            if (namespace is not None and stat.S_ISDIR(namespace[-1])) or artifact is not None:
                return library
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
            library = self.resolve_library(name)
            if library is None:
                raise ReflectionUnavailable('Unresolved native import: ' + name)
            if not (library / (str(relative) + '.olean')).is_file():
                raise ReflectionUnavailable('Selected native namespace has no module artifact: ' + name)
            metadata_path = library / (str(relative) + '.ilean')
            metadata_hash = self.hash_file(metadata_path)
            metadata_cache = getattr(self.observations, 'metadata_cache', None)
            if metadata_cache is not None and metadata_hash in metadata_cache:
                metadata = metadata_cache[metadata_hash]
            else:
                metadata = read_json(metadata_path)
            self.hash_file(metadata_path)  # Parsing must observe the same file.
            if metadata_cache is not None:
                metadata_cache[metadata_hash] = metadata
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
                     'source': self.observations.hash_file(source) if source else None,
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
    if expected[:1] == ['lean'] and len(actual) == len(expected):
        if Path(actual[0]).name != 'lean':
            return False
        actual[0] = 'lean'
    if expected[:3] == ['lake', 'env', 'lean'] and len(actual) == len(expected):
        if Path(actual[2]).name != 'lean':
            return False
        actual[2] = 'lean'
    if len(actual) == len(expected):
        for index, argument in enumerate(expected):
            if argument == '<generated-input>':
                if not str(actual[index]).endswith('.lean'):
                    return False
                actual[index] = argument
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
        eligible = reuse(before) if callable(reuse) else reuse
        record = self.lookup(before) if eligible else None
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
