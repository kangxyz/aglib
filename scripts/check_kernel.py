#!/usr/bin/env python3
"""Bounded exact-module batches using the installed LeanChecker replay function."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from cache_key import config_hash
from check_compiled_inventory import check_inventory
from library_sources import audit_sources, source_modules, test_modules, module_name, module_path
from resource_guard import run, limits
from run_style_linter import lake_environment

ROOT = Path(__file__).resolve().parents[1]
LEGACY_RUNNER_SHA256 = '7398cde2b7fe41af9961c2fd6a0895e4720becb9a5e1de8a5e1fdda452cde8e5'
LEGACY_DRIVER_SHA256 = '063ab4389662ffa0f7d93dd6c287a005f10a007d5a0c768d738fc777d6f01eaa'
CHECK_ONE = '''unsafe def checkOne (text : String) : IO (String × Nat) := do
  let name := text.toName
  let file ← findOLean name
  let mut files := #[file]
  let server := OLeanLevel.server.adjustFileName file
  if ← server.pathExists then
    files := files.push server
    let privateFile := OLeanLevel.private.adjustFileName file
    if ← privateFile.pathExists then files := files.push privateFile
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then throw <| IO.userError "no module data parts" else
    let count := parts[parts.size - 1].1.constNames.size
    if count > 0 then replayFromImports name
    return (text, count)
'''
DRIVER = '''import LeanChecker
open Lean
namespace AglibKernelBatch
''' + CHECK_ONE + '''
unsafe def checkBatch : IO Unit := do
  initSearchPath (← findSysroot)
  let some text ← IO.getEnv "AGLIB_KERNEL_MODULES"
    | throw <| IO.userError "missing exact module identities"
  let some boundText ← IO.getEnv "AGLIB_KERNEL_MAX_TASKS"
    | throw <| IO.userError "missing batch bound"
  let some bound := boundText.toNat?
    | throw <| IO.userError "invalid batch bound"
  let names := (text.splitOn "\\n").filter (· != "")
  if names.isEmpty || names.length > bound then
    throw <| IO.userError "invalid bounded exact-module batch"
  let mut seen : Array String := #[]
  let mut tasks := #[]
  for name in names do
    if seen.contains name then throw <| IO.userError "duplicate exact module"
    seen := seen.push name
    tasks := tasks.push (name, ← IO.asTask (checkOne name))
  let mut results := #[]
  let mut errors : Array String := #[]
  -- Join every task, including after an error. No success marker precedes this barrier.
  for (name, task) in tasks do
    match task.get with
    | .ok result => results := results.push result
    | .error error => errors := errors.push s!"module {name}: {error}"
  unless errors.isEmpty do
    throw <| IO.userError (String.intercalate "\\n" errors.toList)
  for (name, count) in results do
    IO.println s!"AGLIB_KERNEL_CHECKED {name} {count}"
end AglibKernelBatch
-- Never execute the imported prefix-expanding LeanChecker.main.
#eval AglibKernelBatch.checkBatch
'''


# Metadata only: read import arrays without importing/replaying project proofs.
IMPORT_DRIVER = '''import Lean
open Lean
-- Return no ModuleData references; copied names outlive the mapped parts.
@[noinline] def readDetachedImports (files : Array System.FilePath) :
    IO (Array String × Array CompactedRegion) := do
  let parts ← readModuleDataParts files
  let mut imports : Array String := #[]
  let mut regions : Array CompactedRegion := #[]
  for (part, region) in parts do
    regions := regions.push region
    for imp in part.imports do
      let dependency := String.ofList imp.module.toString.toList
      if !imports.contains dependency then imports := imports.push dependency
  return (imports, regions)

unsafe def inspectImports : IO Unit := do
  initSearchPath (← findSysroot)
  let some text ← IO.getEnv "AGLIB_KERNEL_MODULES"
    | throw <| IO.userError "missing metadata roots"
  let mut pending := (text.splitOn "\n").filter (· != "") |>.toArray
  let mut seen : Std.HashSet String := {}
  let srcPath ← getSrcSearchPath
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let file ← findOLean name.toName
    let mut files := #[file]
    let server := OLeanLevel.server.adjustFileName file
    if ← server.pathExists then
      files := files.push server
      let priv := OLeanLevel.private.adjustFileName file
      if ← priv.pathExists then files := files.push priv
    let (imports, regions) ← readDetachedImports files
    -- ModuleData references ended in the noinline helper; strings are copied.
    -- Later parts may reference earlier parts, so release in reverse order.
    for region in regions.reverse do region.free
    pending := pending ++ imports
    let source ← try pure (Json.str (← findLean srcPath name.toName).toString)
                  catch _ => pure Json.null
    IO.println <| "AGLIB_KERNEL_IMPORTS " ++ (Json.mkObj [
      ("module", toJson name), ("artifacts", toJson (files.map (·.toString))),
      ("source", source), ("imports", toJson imports)]).compress
#eval inspectImports
'''


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def json_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n')


def expected_sources(root, client=False):
    if client:
        return {Path('Consumer.lean')} | {
            path.relative_to(root) for path in (root / 'Consumer').rglob('*.lean')}
    return source_modules(root) | test_modules(root) | {Path('AglibTest/AuditSupport.lean')}


def artifact_hashes(root, module, file_digest=digest):
    base = root / '.lake/build/lib/lean' / module_path(module).with_suffix('.olean')
    if not base.is_file():
        raise RuntimeError('Missing exact module artifact: ' + str(base))
    return {str(path.relative_to(root)): file_digest(path)
            for path in [base, Path(str(base) + '.server'), Path(str(base) + '.private')]
            if path.is_file()}


def proof_basis(root, prefix, client=False, file_digest=digest, selected=None):
    enrolled = expected_sources(root, client)
    allowed = enrolled
    if selected is not None:
        requested = {module_path(name) for name in selected}
        if not requested or not requested <= enrolled:
            raise RuntimeError('Probe contains duplicate or unenrolled exact module')
        enrolled = requested
    if client:
        library = root / '.lake/build/lib/lean'
        actual = {path.relative_to(library).with_suffix('.lean')
                  for path in (library / 'Consumer').rglob('*.olean')}
        if (library / 'Consumer.olean').is_file():
            actual.add(Path('Consumer.lean'))
        if (actual != enrolled if selected is None else not enrolled <= actual or bool(actual - allowed)):
            raise RuntimeError('Independent client compiled inventory differs from current source')
        sources = enrolled | ({Path('Audit.lean')} if selected is None and (root / 'Audit.lean').is_file() else set())
    else:
        errors = check_inventory(root, selected) if selected is not None else check_inventory(root)
        if errors:
            raise RuntimeError('\n'.join(errors))
        sources = enrolled if selected is not None else source_modules(root) | test_modules(root) | audit_sources(root)
    modules = sorted(module_name(path) for path in enrolled)
    if len(set(modules)) != len(enrolled):
        raise RuntimeError('Nonunique exact-module enrollment')
    return {'format_version': 2, 'root': str(root), 'modules': modules,
            'source_hashes': {str(path): file_digest(root / path) for path in sorted(sources)},
            'artifact_hashes': {name: artifact_hashes(root, name, file_digest) for name in modules},
            'config_hashes': {name: file_digest(root / name) for name in
                              ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']},
            'check_one_sha256': hashlib.sha256(CHECK_ONE.encode()).hexdigest(),
            'driver_sha256': hashlib.sha256(DRIVER.encode()).hexdigest(),
            'semantics': 'installed LeanChecker.replayFromImports; last-most-private part; empty is vacuous',
            'installed_LeanChecker_sha256': file_digest(prefix / 'lib/lean/LeanChecker.olean'),
            'installed_LeanChecker_source_sha256': file_digest(prefix / 'src/lean/LeanChecker.lean')}


def portable_path(path, root, prefix):
    # Keep lexical package paths: a coherent checkout may use symlinked caches.
    path = Path(os.path.abspath(path))
    for label, base in [('root', root), ('toolchain', prefix)]:
        try:
            return label + ':' + path.relative_to(base).as_posix()
        except ValueError:
            try:
                return label + ':' + path.resolve().relative_to(base).as_posix()
            except ValueError:
                pass
    return 'external:' + str(path.resolve())


def file_stamp(path):
    def fields(info):
        return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
    try:
        return (fields(path.lstat()), fields(path.stat()))
    except FileNotFoundError:
        return None


def search_paths(root, prefix, environment, source=False):
    key = 'LEAN_SRC_PATH' if source else 'LEAN_PATH'
    paths = [Path(os.path.abspath(root / item)) for item in
             environment.get(key, '').split(os.pathsep) if item]
    return paths + ([prefix / 'src/lean/lake', prefix / 'src/lean'] if source else
                    [root / '.lake/build/lib/lean', prefix / 'lib/lean'])


def runtime_paths(prefix, lean):
    return [Path(lean)] + sorted(path for path in (prefix / 'lib').rglob('*')
                               if path.is_file() and path.suffix in {'.so', '.dylib', '.dll'})


def module_facets(base):
    return [base, Path(str(base) + '.server'), Path(str(base) + '.private'),
            base.with_suffix('.ir.sig'), base.with_suffix('.ir')]


def metadata_fence(root, prefix, lean, environment):
    # One initial stat sweep fences the still-unknown compiled import graph.
    # No tree walk or whole-file hashing is repeated between replay batches.
    paths = set(runtime_paths(prefix, lean))
    for tree in search_paths(root, prefix, environment):
        paths.add(tree)
        for parent, dirs, files in os.walk(tree):
            paths.add(Path(parent))
            paths.update(Path(parent) / name for name in dirs)
            paths.update(Path(parent) / name for name in files if
                         name.endswith(('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig')))
    return {path.resolve(): file_stamp(path) for path in paths}


def input_paths(root, prefix, lean, environment, client, graph, selected=None):
    sources = {module_path(name) for name in selected} if selected is not None else expected_sources(root, client) | audit_sources(root)
    paths = {root / path for path in sources}
    paths.update(root / name for name in ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json'])
    paths.update(runtime_paths(prefix, lean))
    compiled = set()
    for node in graph.values():
        base = Path(os.path.abspath(root / node['artifacts'][0]))
        compiled.update(module_facets(base))
        if node['source'] is not None:
            paths.add(Path(os.path.abspath(root / node['source'])))
    paths.update(compiled)
    roots = set(search_paths(root, prefix, environment) + search_paths(root, prefix, environment, True))
    # Lean resolves a namespace root first, rather than trying every module file.
    # Watch all such candidates, including currently absent shadowing roots.
    namespaces = {name.split('.')[0] for name in graph}
    for source in [False, True]:
        for search in search_paths(root, prefix, environment, source):
            paths.update(search / (name + suffix) for name in namespaces
                         for suffix in ['', '.lean' if source else '.olean'])
    stops = {path.resolve() for path in roots | {root, prefix}}
    for path in list(paths):
        parent = path.parent
        while parent != parent.parent:
            paths.add(parent)
            if parent.resolve() in stops:
                break
            parent = parent.parent
    return paths, compiled


def drift_snapshot(paths):
    # ctime/inode detect changed-and-restored files even with restored mtimes.
    return {path: file_stamp(path) for path in paths}


def import_graph(root, prefix, lean, environment, directory, modules):
    number = 0
    while any(directory.glob(f'imports-{number:04}.*')):
        number += 1
    stem = f'imports-{number:04}'
    output, resource = directory / (stem + '.log'), directory / (stem + '.resource.json')
    budget = dict(limits(), lean_threads=1)
    with tempfile.TemporaryDirectory(prefix='aglib-imports-') as temporary:
        driver = Path(temporary) / 'Imports.lean'
        driver.write_text(IMPORT_DRIVER)
        env = dict(os.environ, **environment, LEAN_SYSROOT=str(prefix),
                   AGLIB_KERNEL_MODULES='\n'.join(sorted(set(modules) | {'LeanChecker'})))
        with output.open('x') as log:
            code = run([lean, '-j1', '-M' + str(budget['lean_memory_mb']), str(driver)],
                       cwd=root, env=env, receipt=resource, budget=budget,
                       stdout=log, stderr=subprocess.STDOUT)
    guard = json.loads(resource.read_text())
    if code or guard['exit_code'] != 0 or guard['guard_failure'] is not None \
            or not guard['owned_group_gone']:
        raise RuntimeError('Compiled import metadata failed; inspect ' + str(output))
    graph = {}
    for line in output.read_text().splitlines():
        if not line.startswith('AGLIB_KERNEL_IMPORTS '):
            continue
        node = json.loads(line.removeprefix('AGLIB_KERNEL_IMPORTS '))
        name = node['module']
        if name in graph or not node['artifacts'] or len(set(node['imports'])) != len(node['imports']):
            raise RuntimeError('Incomplete or duplicate compiled import metadata')
        graph[name] = node
    if not (set(modules) | {'LeanChecker'}) <= graph.keys():
        raise RuntimeError('Missing compiled import metadata roots')
    for node in graph.values():
        if not set(node['imports']) <= graph.keys():
            raise RuntimeError('Incomplete compiled import dependency closure')
    return graph


def closure_basis(root, prefix, lean, environment, client, graph, selected=None):
    hashes = {}
    def once(path):
        path = Path(path).resolve()
        if path not in hashes:
            hashes[path] = digest(path)
        return hashes[path]
    basis = proof_basis(root, prefix, client, file_digest=once, selected=selected)
    files = {}
    def identity(path):
        path = Path(path)
        if not path.is_absolute():
            path = root / path
        key = portable_path(path, root, prefix)
        if key not in files:
            files[key] = once(path)
        return key
    for name, expected in [(name, root / '.lake/build/lib/lean' / module_path(name).with_suffix('.olean'))
                           for name in basis['modules']] + [('LeanChecker', prefix / 'lib/lean/LeanChecker.olean')]:
        if name not in graph or Path(root / graph[name]['artifacts'][0]).resolve() != expected.resolve():
            raise RuntimeError('Compiled import metadata resolved an unexpected enrolled/checker artifact: ' + name)
    nodes = {}
    for name, node in sorted(graph.items()):
        source = node['source']
        source_path = (root / source) if source is not None else None
        nodes[name] = {'imports': sorted(node['imports']),
                       'artifacts': [identity(path) for path in module_facets(Path(root / node['artifacts'][0]))
                                     if path.is_file()],
                       'source': identity(source_path) if source_path is not None and source_path.is_file() else None}
    # Include the executable and native runtime libraries, as well as the
    # checker import closure. Package pins alone do not identify installed code.
    runtime = runtime_paths(prefix, lean)
    runtime_hashes = {identity(path): files[identity(path)] for path in runtime}
    visiting, keys = set(), {}
    def key(name):
        if name in keys:
            return keys[name]
        if name in visiting or name not in nodes:
            raise RuntimeError('Cyclic or incomplete compiled import metadata')
        visiting.add(name)
        node = nodes[name]
        imports = {dep: key(dep) for dep in node['imports']}
        visiting.remove(name)
        keys[name] = None if node['source'] is None or None in imports.values() else json_hash({
            'source': [node['source'], files[node['source']]],
            'artifacts': {path: files[path] for path in node['artifacts']}, 'imports': imports})
        return keys[name]
    for name in nodes:
        key(name)
    semantics = {'schema': 'compiled-import-closure-v1', 'config': config_hash(root, packages=('',)),
                 'runtime': runtime_hashes, 'checker_closure': keys['LeanChecker'],
                 'check_one_sha256': basis['check_one_sha256'],
                 'driver_sha256': basis['driver_sha256'], 'semantics': basis['semantics']}
    basis.update(format_version=3, dependency_graph=nodes, dependency_file_hashes=files,
                 replay_inputs=semantics,
                 module_inputs={name: json_hash([semantics, keys[name]])
                                if keys[name] is not None and keys['LeanChecker'] is not None else None
                                for name in basis['modules']})
    return basis


def saved_basis(directory, basis):
    initial = directory / 'basis.json'
    target = initial if not initial.exists() or json.loads(initial.read_text()) == basis else \
        directory / 'snapshots' / json_hash(basis) / 'basis.json'
    if target.exists():
        if json.loads(target.read_text()) != basis:
            raise RuntimeError('Changed immutable replay basis')
    else:
        write_json(target, basis)
    return target


def confined(directory, relative):
    path = directory / relative
    if not path.resolve().is_relative_to(directory.resolve()):
        raise RuntimeError('Replay evidence escaped its explicit receipt lineage')
    return path


def previous_records(directory, modules):
    # Only the explicitly selected lineage's current summaries; no history scan.
    result = {}
    summaries = [directory / name for name in ['coverage.json', 'probe.json']
                 if (directory / name).exists()]
    for path in sorted(summaries, key=lambda path: path.stat().st_mtime_ns):
        summary = json.loads(path.read_text())
        result.update(summary.get('module_records', {}))
    initial = directory / 'basis.json'
    if initial.exists():
        old = json.loads(initial.read_text())
        for name in set(modules) & set(old['modules']):
            path = record_path(directory, old['modules'], name)
            if name not in result and path.exists():
                result[name] = str(path.relative_to(directory))
    return result


def reusable_record(directory, relative, name, basis, basis_cache=None):
    record = json.loads(confined(directory, relative).read_text())
    if record['module'] != name:
        raise RuntimeError('Receipt module identity mismatch')
    original_file = confined(directory, record.get('basis', 'basis.json'))
    basis_cache = {} if basis_cache is None else basis_cache
    if original_file not in basis_cache:
        original = json.loads(original_file.read_text())
        basis_cache[original_file] = original, json_hash(original)
    original, original_hash = basis_cache[original_file]
    validate_record(record, directory, original_hash)
    if record.get('format_version') == 3:
        expected = original['module_inputs'].get(name)
        if expected != record.get('module_input_sha256'):
            raise RuntimeError('Module receipt differs from its original closure basis')
        return record if expected is not None and expected == basis['module_inputs'].get(name) else None
    # Old evidence lacks compiled dependency metadata. Preserve/import it, but
    # obtain a new closure-bound replay before reusing it.
    return None


def parse_markers(text, expected):
    found = {}
    for line in text.splitlines():
        if not line.startswith('AGLIB_KERNEL_CHECKED '):
            continue
        parts = line.split()
        if len(parts) != 3 or parts[1] not in expected or parts[1] in found \
                or not parts[2].isdigit():
            raise RuntimeError('Malformed, duplicate, or unexpected kernel success marker')
        found[parts[1]] = int(parts[2])
    if set(found) != set(expected):
        raise RuntimeError('Kernel success markers do not exactly match the batch')
    return found


def record_path(directory, modules, name):
    return directory / ('module-' + str(modules.index(name)).zfill(4) + '.json')


def validate_record(record, directory, basis_hash):
    if record.get('status') != 'passed' or record.get('proof_basis_sha256') != basis_hash:
        raise RuntimeError('Incomplete or different-basis module receipt')
    evidence = record['evidence_hashes']
    if not {record['log'], record['resource']} <= evidence.keys():
        raise RuntimeError('Missing hashed replay log/resource evidence')
    for relative, expected in evidence.items():
        if digest(confined(directory, relative)) != expected:
            raise RuntimeError('Changed module replay evidence: ' + relative)
    resource = json.loads(confined(directory, record['resource']).read_text())
    if resource['exit_code'] != 0 or resource['guard_failure'] is not None \
            or not resource['owned_group_gone']:
        raise RuntimeError('Module resource receipt is not a closed successful attempt')
    names = record['attempt_modules']
    if len(names) != len(set(names)) or record['module'] not in names:
        raise RuntimeError('Invalid original attempt module identities')
    counts = parse_markers(confined(directory, record['log']).read_text(), names)
    if counts[record['module']] != record['new_constants']:
        raise RuntimeError('Module count differs from its actual success marker')


def adopt_legacy(directory, legacy, source_basis_file, runner_file, basis):
    if source_basis_file is None or runner_file is None:
        raise RuntimeError('Legacy adoption requires frozen full-source basis and audited runner source')
    if digest(runner_file) != LEGACY_RUNNER_SHA256:
        raise RuntimeError('Unrecognized legacy Python runner')
    raw = json.loads((legacy / 'basis.json').read_text())
    if raw.get('driver_sha256') != LEGACY_DRIVER_SHA256:
        raise RuntimeError('Unrecognized legacy embedded Lean driver')
    for key in ['root', 'modules', 'artifact_hashes', 'config_hashes',
                'installed_LeanChecker_sha256', 'installed_LeanChecker_source_sha256']:
        if raw[key] != basis[key]:
            raise RuntimeError('Legacy proof basis changed: ' + key)
    if raw['source_hashes'] != {str(module_path(name)): basis['source_hashes'][str(module_path(name))]
                                for name in basis['modules']}:
        raise RuntimeError('Legacy enrolled source basis changed')
    full = json.loads(source_basis_file.read_text())
    if full['root'] != basis['root'] or full['source_hashes'] != basis['source_hashes']:
        raise RuntimeError('Legacy full-source basis changed')
    raw_dir = directory / 'legacy-raw'
    raw_dir.mkdir(parents=True, exist_ok=True)
    for source, target in [(legacy / 'basis.json', raw_dir / 'basis.json'),
                           (source_basis_file, raw_dir / 'full-source-basis.json'),
                           (runner_file, raw_dir / 'runner.py')]:
        shutil.copyfile(source, target)
    common_evidence = {str(path.relative_to(directory)): digest(path) for path in
                       [raw_dir / 'basis.json', raw_dir / 'full-source-basis.json', raw_dir / 'runner.py']}
    adopted = []
    for index, name in enumerate(basis['modules']):
        filename = 'module-' + str(index).zfill(4)
        old_file = legacy / (filename + '.json')
        if not old_file.exists():
            continue
        old = json.loads(old_file.read_text())
        resource_file = legacy / ('resource-' + str(index).zfill(4) + '.json')
        log_file = Path(old['log'])
        resource = json.loads(resource_file.read_text())
        if old['module'] != name or old['status'] != 'passed' or resource['limits'] != raw['limits']:
            raise RuntimeError('Invalid legacy module/profile record: ' + name)
        if resource['exit_code'] != 0 or resource['guard_failure'] is not None \
                or not resource['owned_group_gone']:
            raise RuntimeError('Unsuccessful legacy resource record: ' + name)
        if parse_markers(log_file.read_text(), [name])[name] != old['new_constants']:
            raise RuntimeError('Legacy marker/count mismatch: ' + name)
        saved = dict(common_evidence)
        for source, suffix in [(old_file, '.module.json'), (resource_file, '.resource.json'),
                               (log_file, '.log')]:
            target = raw_dir / (filename + suffix)
            shutil.copyfile(source, target)
            saved[str(target.relative_to(directory))] = digest(target)
        record = dict(old, format_version=2, proof_basis_sha256=json_hash(basis),
                      log='legacy-raw/' + filename + '.log',
                      resource='legacy-raw/' + filename + '.resource.json',
                      attempt_modules=[name], evidence_hashes=saved,
                      execution_profile={'limits': resource['limits'], 'batch_size': 1,
                                         'driver_sha256': raw['driver_sha256']},
                      adopted_from={'runner_sha256': LEGACY_RUNNER_SHA256,
                                    'basis_sha256': digest(legacy / 'basis.json')})
        target = record_path(directory, basis['modules'], name)
        if target.exists() and json.loads(target.read_text()) != record:
            raise RuntimeError('Adoption would replace an existing different record')
        write_json(target, record)
        adopted.append(name)
    write_json(directory / 'legacy-adoption.json', {'recognized_runner_sha256': LEGACY_RUNNER_SHA256,
        'recognized_driver_sha256': LEGACY_DRIVER_SHA256, 'proof_basis_sha256': json_hash(basis),
        'raw_basis_sha256': digest(raw_dir / 'basis.json'), 'adopted_modules': adopted,
        'boundary': 'Original single-task profiles and raw records preserved, not relabeled as batches.'})


def replay(root, directory, only=None, client=False, *, selected=None, batch_size=None,
           legacy=None, legacy_sources=None, legacy_runner=None):
    root = root.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    available = os.cpu_count() or 1
    batch_size = int(os.environ.get('AGLIB_KERNEL_BATCH_SIZE', min(4, available))
                     if batch_size is None else batch_size)
    if not 1 <= batch_size <= available:
        raise RuntimeError('Batch size must be positive and fit available logical CPUs')
    environment = dict(lake_environment(root))
    lean = environment.pop('lean')
    prefix = Path(subprocess.check_output([lean, '--print-prefix'], text=True).strip())
    prefix = prefix.resolve()
    if Path(lean).resolve() != (prefix / 'bin/lean').resolve():
        raise RuntimeError('Lake executable differs from installed pinned compiler')
    fence = metadata_fence(root, prefix, lean, environment)
    enrolled = sorted(module_name(path) for path in expected_sources(root, client))
    requested = [only] if only is not None else (list(selected) if selected is not None else None)
    if requested is not None and (not requested or len(set(requested)) != len(requested)
                                  or not set(requested) <= set(enrolled)):
        raise RuntimeError('Probe contains duplicate or unenrolled exact module')
    modules = requested if requested is not None else enrolled
    graph = import_graph(root, prefix, lean, environment, directory, modules)
    watched, compiled = input_paths(root, prefix, lean, environment, client, graph, requested)
    before = drift_snapshot(watched)
    if any(before[path] != fence.get(path.resolve()) for path in watched
           if path.resolve() in fence or path in compiled):
        raise RuntimeError('Compiled metadata inputs changed during extraction')
    basis = closure_basis(root, prefix, lean, environment, client, graph, requested)
    def stable():
        if drift_snapshot(watched) != before:
            raise RuntimeError('Source/artifact/checker/config basis changed during replay')
    stable()
    modules = basis['modules']
    wanted = [only] if only is not None else (list(selected) if selected is not None else modules)
    if not wanted or len(set(wanted)) != len(wanted) or not set(wanted) <= set(modules):
        raise RuntimeError('Probe contains duplicate or unenrolled exact module')
    if legacy is not None:
        if saved_basis(directory, basis).parent != directory:
            raise RuntimeError('Legacy adoption requires its own original-basis receipt directory')
        adopt_legacy(directory, legacy, legacy_sources, legacy_runner, basis)
    completed, basis_cache = {}, {}
    references = previous_records(directory, modules)
    for name in wanted:
        if name in references:
            record = reusable_record(directory, references[name], name, basis, basis_cache)
            if record is not None:
                completed[name] = record
    basis_file = saved_basis(directory, basis)
    record_directory = basis_file.parent
    pending = [name for name in wanted if name not in completed]
    with tempfile.TemporaryDirectory(prefix='aglib-kernel-') as temporary:
        driver = Path(temporary) / 'CheckBatch.lean'
        driver.write_text(DRIVER)
        attempt = 0
        def check_batch(names):
            nonlocal attempt
            while any(directory.glob('batch-' + str(attempt).zfill(4) + '.*')):
                attempt += 1
            number = attempt; attempt += 1
            stem = 'batch-' + str(number).zfill(4)
            budget = dict(limits(), lean_threads=len(names))
            env = dict(os.environ, **environment, AGLIB_KERNEL_MODULES='\n'.join(names),
                       AGLIB_KERNEL_MAX_TASKS=str(len(names)), LEAN_NUM_THREADS=str(len(names)),
                       LEAN_SYSROOT=str(prefix))
            output, resource_file = directory / (stem + '.log'), directory / (stem + '.resource.json')
            command = [lean, '-j' + str(len(names)), '-M' + str(budget['lean_memory_mb']), str(driver)]
            with output.open('x') as log:
                code = run(command, cwd=root, env=env, receipt=resource_file,
                           budget=budget, stdout=log, stderr=subprocess.STDOUT)
            resource = json.loads(resource_file.read_text())
            stable()
            metadata = {'modules': names, 'exit_code': code, 'resource': resource_file.name,
                        'log': output.name, 'execution_profile': {'limits': budget, 'batch_size': len(names),
                        'driver_sha256': hashlib.sha256(DRIVER.encode()).hexdigest()}}
            write_json(directory / (stem + '.json'), metadata)
            if code:
                if resource['guard_failure'] == 'owned process group exceeded RSS cutoff' \
                        and resource['owned_group_gone'] and len(names) > 1:
                    middle = max(1, len(names) // 2)
                    print(f'Resource-limited batch of {len(names)}: retry smaller closed batches', flush=True)
                    check_batch(names[:middle]); check_batch(names[middle:]); return
                raise RuntimeError(f'Exact batch failed ({code}); inspect {output}')
            if resource['exit_code'] != 0 or resource['guard_failure'] is not None or not resource['owned_group_gone']:
                raise RuntimeError('Zero exit without successful closed resource guard')
            counts = parse_markers(output.read_text(), names)
            evidence = {output.name: digest(output), resource_file.name: digest(resource_file)}
            for name in names:
                count = counts[name]
                record = {'format_version': 3, 'module': name, 'status': 'passed', 'new_constants': count,
                    'semantics': 'vacuous: last most-private module part is empty' if count == 0
                    else 'installed LeanChecker.replayFromImports', 'proof_basis_sha256': json_hash(basis),
                    'basis': str(basis_file.relative_to(directory)),
                    'module_input_sha256': basis['module_inputs'][name],
                    'attempt_modules': names, 'log': output.name, 'resource': resource_file.name,
                    'execution_profile': metadata['execution_profile'], 'evidence_hashes': evidence}
                target = record_path(record_directory, modules, name)
                if target.exists():
                    # A nonreusable (unknown-source) record still remains immutable.
                    target = record_directory / (target.stem + '-' + stem + '.json')
                write_json(target, record)
                references[name] = str(target.relative_to(directory))
                completed[name] = record
            print(f'Kernel coverage {len(completed)}/{len(wanted)}: batch {len(names)} passed', flush=True)
        for start in range(0, len(pending), batch_size):
            check_batch(pending[start:start + batch_size])
    stable()
    final_environment = dict(lake_environment(root))
    final_lean = final_environment.pop('lean')
    if final_lean != lean or final_environment != environment or \
            closure_basis(root, prefix, lean, environment, client, graph, requested) != basis:
        raise RuntimeError('Source/artifact/checker/config basis changed after replay')
    stable()
    summary = {'status': 'probe passed' if only is not None or selected is not None else 'passed',
               'expected_modules': len(enrolled), 'selected_modules': len(wanted), 'covered_modules': len(completed),
               'new_constants': sum(x['new_constants'] for x in completed.values()),
               'vacuous_modules': sum(x['new_constants'] == 0 for x in completed.values()),
               'proof_basis_sha256': json_hash(basis), 'basis': str(basis_file),
               'semantics': basis['semantics'], 'requested_batch_size': batch_size,
               'execution_profiles_preserved_per_module': True,
               'module_records': {name: path for name, path in references.items() if name in modules},
               'reused_modules': len(wanted) - len(pending),
               'evidence_basis_preserved_per_module': True,
               'adopted_modules': sum('adopted_from' in x for x in completed.values())}
    write_json(directory / ('probe.json' if only is not None or selected is not None else 'coverage.json'), summary)
    print(json.dumps(summary), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--receipt-dir', type=Path, required=True)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--only', help='one enrolled probe; cannot claim full coverage')
    group.add_argument('--modules', nargs='+', help='explicit probe subset; cannot claim full coverage')
    parser.add_argument('--client', action='store_true')
    parser.add_argument('--batch-size', type=int)
    parser.add_argument('--adopt-legacy', type=Path)
    parser.add_argument('--legacy-source-basis', type=Path)
    parser.add_argument('--legacy-runner', type=Path)
    args = parser.parse_args()
    try:
        replay(args.root, args.receipt_dir, args.only, args.client, selected=args.modules,
               batch_size=args.batch_size, legacy=args.adopt_legacy,
               legacy_sources=args.legacy_source_basis, legacy_runner=args.legacy_runner)
        return 0
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError, KeyError) as error:
        print('Bounded kernel replay failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
