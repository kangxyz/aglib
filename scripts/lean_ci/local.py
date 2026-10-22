"""Native Lake final checks with compatible per-command success reuse."""
from contextlib import nullcontext
import fcntl
import os
from pathlib import Path
import subprocess
import uuid

from . import build
from .runtime import NativeRuntime, semantic_environment, semantic_toolchain
from .state import (CheckInputs, Progress, ReflectionGraph, TemporalInputs, check_binding,
                    valid_receipt, write_json)
from .source import lean_imports, module_path

AUDITOR_REVISION = '46024e005996495c65ef609368e11ab39c4222e3'
CONFIG = ('lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json')
TOOLS = ('batteries/runLinter', 'mathlib/lint-style', 'mathlib/mk_all')
EXCLUDED = {'.lake', '.git', '__pycache__', 'node_modules', 'vendor'}


def sources(root):
    """Read package inputs, without enrolling caches or another package's clients."""
    paths = []
    for current, children, files in os.walk(root, followlinks=False):
        children[:] = sorted(n for n in children if n not in EXCLUDED and n != 'examples')
        for name in sorted(files):
            path = Path(current) / name
            if path.suffix == '.lean' or path.relative_to(root).as_posix() in CONFIG:
                if path.is_symlink():
                    raise ValueError('Native source inputs must be regular files: ' + str(path))
                paths.append(path)
    return sorted(paths)


def changed_paths(root, base=None, head=None):
    """Optional local range, never a GitHub success/baseline protocol."""
    try:
        repository = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'],
                          cwd=root, text=True, stderr=subprocess.DEVNULL).strip())
    except subprocess.CalledProcessError:
        if base or head:
            raise ValueError('A Git range requires a Git checkout; omit it in a transported package')
        return None
    if head:
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
        requested = subprocess.check_output(['git', 'rev-parse', head], cwd=root, text=True).strip()
        if actual != requested or subprocess.check_output(['git', 'status', '--porcelain'], cwd=root).strip():
            raise ValueError('--head requires the clean selected checkout')
    args = ['git', 'diff', '--name-only', '-z', '--no-renames', base or 'HEAD']
    if head:
        args.append(head)
    changed = subprocess.check_output(args, cwd=root).decode().split('\0')
    if not head:
        changed += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z'],
                                            cwd=root).decode().split('\0')
    prefix = root.relative_to(repository).as_posix()
    return sorted({name[len(prefix) + 1:] if prefix != '.' and name.startswith(prefix + '/') else name
                   for name in changed if name and (prefix == '.' or name.startswith(prefix + '/'))})


def documentation_only(changed):
    return bool(changed) and all(Path(name).suffix in {'.md', '.rst', '.txt', '.bib', '.tex'}
                                 and not name.startswith(('scripts/', '.github/')) for name in changed)


def commands(root, production, check_targets=(), source_checks=()):
    """The same native commands as the public workflow, without its job transport."""
    if not production:
        raise ValueError('At least one production root is required')
    for name in (*production, *check_targets):
        module_path(name)
    return [*map(list, source_checks),
            ['lake', '--rehash', 'build', *production],
            ['lake', '--rehash', 'build', *TOOLS, *check_targets],
            ['lake', 'test'],
            *[['lake', '--no-build', 'exe', 'mathlib/mk_all', '--lib', name, '--check'] for name in production],
            ['lake', '--no-build', 'exe', 'mathlib/lint-style', *production],
            ['lake', '--no-build', 'lint', *production, '--', '--trace'],
            *[['lake', 'env', '<pinned-axiom-audit>', '--root', name] for name in production]]


def _run(runtime, command, directory, *, cwd=None):
    directory.mkdir(parents=True, exist_ok=False)
    result = runtime.run({'id': directory.name, 'kind': 'process', 'command': list(map(str, command)),
                          'cwd': str(cwd or runtime.root)}, directory)
    receipt = result.get('receipt')
    if not valid_receipt(receipt, command, cwd or runtime.root):
        raise ValueError('Native command has no completed successful receipt: ' + str(command))
    return receipt


def _observe_sources(root, observations):
    paths = sources(root)
    for path in paths:
        observations.hash_file(path)
    for name in CONFIG:
        observations.optional_hash(root / name)
    for directory in {root, *(path.parent for path in paths)}:
        observations.observe_directory(directory, EXCLUDED)
    return paths


def _prepare_auditor(root, runtime, directory, observations):
    selected = runtime.environment.get('LEAN_CI_AUDITOR_ROOT')
    tool = Path(selected).expanduser().resolve() if selected else root / '.lake/axiom-audit'
    if not (tool / '.git').exists():
        if selected:
            raise ValueError('LEAN_CI_AUDITOR_ROOT must be a pinned prepared checkout')
        _run(runtime, ['git', 'clone', '--depth', '1', '--branch', 'v0.1.2',
                       'https://github.com/leanprover-community/axiom-audit.git', str(tool)], directory / 'clone')
    revision = subprocess.check_output(['git', '-C', str(tool), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != AUDITOR_REVISION:
        raise ValueError('Unexpected axiom-audit source revision: ' + revision)
    dirty = subprocess.check_output(['git', '-C', str(tool), 'diff', '--name-only',
                                     'HEAD', '--', '*.lean', 'lakefile.toml'])
    if dirty.strip():
        raise ValueError('The pinned auditor sources have local modifications')
    expected = (root / 'lean-toolchain').read_bytes()
    pin = tool / 'lean-toolchain'
    if not pin.is_file() or pin.read_bytes() != expected:
        if selected:
            raise ValueError('Prepared auditor toolchain differs from the package')
        pin.write_bytes(expected)
    _run(runtime, ['lake', '--rehash', 'build'], directory / 'build', cwd=tool)
    binary = tool / '.lake/build/bin/axiom-audit'
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise ValueError('The pinned auditor executable is missing')
    return binary


def check(root, production, *, check_targets=(), source_checks=(), base=None, head=None,
          full=False, source_only=False, progress=None, state=None, outputs=None,
          resource_config=None, environment=None, runtime=None):
    root = Path(root).resolve()
    if full and (base or head):
        raise ValueError('--full cannot be combined with a Git range')
    commands(root, production, check_targets, source_checks)
    changes = None if full else changed_paths(root, base, head)
    native = not source_only and not documentation_only(changes)
    if source_only and outputs:
        raise ValueError('--source-only cannot export checked native outputs')
    state = Path(state).resolve() if state else root / '.lake/native-checks'
    progress = Path(progress).resolve() if progress else state / 'progress'
    state.mkdir(parents=True, exist_ok=True)
    with (state / 'lock').open('a') as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        directory = state / ('run-' + uuid.uuid4().hex)
        directory.mkdir()
        summary = {'status': 'running', 'root': str(root), 'production': list(production),
                   'native': native, 'performed_checks': [], 'reused_checks': [], 'directory': str(directory)}
        summary_path = directory / 'result.json'
        write_json(summary_path, summary)
        try:
            _checks(root, production, check_targets, source_checks, native, progress, directory,
                    summary, outputs, runtime or NativeRuntime(root, resource_config, environment))
            summary['status'] = 'complete'
        except BaseException as error:
            summary.update(status='failed', error=str(error))
            raise
        finally:
            write_json(summary_path, summary)
        return summary


def _checks(root, production, check_targets, source_checks, native, progress, directory,
            summary, outputs, runtime):
    whole = TemporalInputs()
    files = _observe_sources(root, whole)
    progress_store = Progress(progress)
    hashes, metadata = {}, {}
    toolchain, search_path = {}, None
    original_environment = dict(runtime.environment)
    source_helpers = [str(path) for path in sorted((root / 'scripts').glob('*.py'))
                      if not path.name.startswith('test_')]
    parser = root / 'scripts/lean_ci/source.py'
    if parser.is_file():
        source_helpers.append(str(parser))
    counter = 0
    accepted = []

    def execute(name, command, *, imports=(), raw=(), enrollment=None, prepared=False):
        nonlocal counter
        counter += 1
        run_dir = directory / f'{counter:03d}-{name}'
        inputs = CheckInputs(whole, hash_cache=hashes, metadata_cache=metadata)
        def binding():
            with inputs.inspection():
                paths = [*CONFIG, *raw]
                for argument in command:
                    candidate = root / argument
                    if candidate.is_file():
                        paths.append(str(candidate))
                native_tools = [path for path in paths if '/.lake/build/bin/' in str(root / path)]
                paths = [path for path in paths if path not in native_tools]
                value = check_binding(root, name, (), command, paths,
                                      toolchain=semantic_toolchain(toolchain), hash_file=inputs.hash_file)
                if enrollment is not None:
                    value['source_enrollment'] = enrollment
                value['environment'] = semantic_environment(
                    {name: original_environment.get(name) for name in
                     ('ELAN_TOOLCHAIN', 'LEAN_OPTIONS', 'LEAN_OPTS', 'LEAN_ARGS',
                      'LAKE_ARGS', 'LEAN_PATH', 'LEAN', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN')}, toolchain)
                if imports and search_path:
                    graph = ReflectionGraph(root, search_path,
                        semantic_toolchain(toolchain, installation=True), inputs)
                    value['reflective_imports'] = graph.closure(imports)
                else:
                    value['reflective_imports'] = None
                if native_tools:
                    value['native_tools'] = {path: inputs.native_optional_hash(root / path)
                                             for path in native_tools}
                if prepared:
                    value['checker'] = inputs.native_hash_file(Path(command[2]))
                return value
        before = binding()
        reusable = not imports or before.get('reflective_imports') is not None
        record = progress_store.lookup(before) if reusable else None
        if record is not None:
            mode = 'reused_checks'
        else:
            receipt = _run(runtime, command, run_dir)
            after = binding()
            if after != before:
                raise ValueError('Native check inputs changed during execution: ' + name)
            inputs.assert_stable()
            record = progress_store.save(before, receipt, command)
            mode = 'performed_checks'
        if binding() != before:
            raise ValueError('Native check inputs changed while consuming success: ' + name)
        inputs.assert_stable()
        accepted.append(inputs.native)
        summary[mode].append(name)
        write_json(directory / 'result.json', summary)

    raw_sources = [str(path.relative_to(root)) for path in files]
    for index, command in enumerate(source_checks):
        execute('source-' + str(index), list(map(str, command)), raw=[*raw_sources, *source_helpers])
    if not native:
        whole.assert_stable()
        return
    # Elan discovery is once per invocation. Resource/process guarding and the
    # parent's managed compiler remain in force for every native command.
    toolchain = runtime.compiler_identity(whole.hash_file)
    context = (build.capped_toolchain(root, build.build_threads(runtime.environment, runtime.resource_config),
                 environment=runtime.environment, config=runtime.resource_config)
               if type(runtime) is NativeRuntime else nullcontext(runtime.environment))
    with context as env:
        bounded = NativeRuntime(root, runtime.resource_config, env)
        if type(runtime) is not NativeRuntime:
            bounded = runtime  # Explicit test executor; never inferred from input.
        runtime = bounded
        mapping = directory / 'native-outputs.jsonl'
        _run(runtime, ['lake', '--rehash', 'build', *production, '-o', str(mapping)], directory / 'build')
        _run(runtime, ['lake', '--rehash', 'build', *TOOLS, *check_targets], directory / 'tools')
        _run(runtime, ['lake', 'test'], directory / 'tests')
        search = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                         cwd=root, env=runtime.environment, text=True).strip()
        search_path = [str((root / path).resolve()) for path in search.split(os.pathsep) if path]
        def checker(name):
            script = root / '.lake/packages/mathlib/scripts' / (name + '.lean')
            binary = root / '.lake/packages/mathlib/.lake/build/bin' / name
            imports = lean_imports(script.read_text()) if script.is_file() else []
            return imports, [str(script), str(binary)]
        def production_sources(name):
            entry = root / module_path(name)
            directory = entry.with_suffix('')
            return [str(path.relative_to(root)) for path in files
                    if path == entry or path.is_relative_to(directory)]
        entry_imports, entry_files = checker('mk_all')
        for name in production:
            execute('entries-' + name,
                    ['lake', '--no-build', 'exe', 'mathlib/mk_all', '--lib', name, '--check'],
                    imports=entry_imports, raw=[str(module_path(name)), *entry_files],
                    enrollment=production_sources(name))
        text_imports, text_files = checker('lint-style')
        execute('text-style', ['lake', '--no-build', 'exe', 'mathlib/lint-style', *production],
                imports=text_imports, raw=[*(path for name in production for path in production_sources(name)),
                                         *text_files, 'scripts/nolints-style.txt'])
        execute('lint', ['lake', '--no-build', 'lint', *production, '--', '--trace'],
                imports=[*production, 'Batteries.Tactic.Lint'],
                raw=['scripts/nolints.json', 'scripts/nolints-style.txt',
                     '.lake/packages/batteries/scripts/runLinter.lean',
                     '.lake/packages/batteries/.lake/build/bin/runLinter'])
        auditor = _prepare_auditor(root, runtime, directory / 'auditor', whole)
        for name in production:
            execute('axioms-' + name, ['lake', 'env', str(auditor), '--root', name],
                    imports=[name], prepared=True)
    # Keep the observations that justified earlier successes alive until export.
    # This is an in-process stat check, not another native validation pass.
    for observations in accepted:
        observations.assert_stable()
    whole.assert_stable()
    if files != sources(root):
        raise ValueError('Package source enrollment changed during native checking')
    if outputs:
        destination = Path(outputs).resolve()
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(mapping.read_bytes())
