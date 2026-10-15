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


def artifact_hashes(root, module):
    base = root / '.lake/build/lib/lean' / module_path(module).with_suffix('.olean')
    if not base.is_file():
        raise RuntimeError('Missing exact module artifact: ' + str(base))
    return {str(path.relative_to(root)): digest(path)
            for path in [base, Path(str(base) + '.server'), Path(str(base) + '.private')]
            if path.is_file()}


def proof_basis(root, prefix, client=False):
    enrolled = expected_sources(root, client)
    if client:
        library = root / '.lake/build/lib/lean'
        actual = {path.relative_to(library).with_suffix('.lean')
                  for path in (library / 'Consumer').rglob('*.olean')}
        if (library / 'Consumer.olean').is_file():
            actual.add(Path('Consumer.lean'))
        if actual != enrolled:
            raise RuntimeError('Independent client compiled inventory differs from current source')
        sources = enrolled | ({Path('Audit.lean')} if (root / 'Audit.lean').is_file() else set())
    else:
        errors = check_inventory(root)
        if errors:
            raise RuntimeError('\n'.join(errors))
        sources = source_modules(root) | test_modules(root) | audit_sources(root)
    modules = sorted(module_name(path) for path in enrolled)
    if len(set(modules)) != len(enrolled):
        raise RuntimeError('Nonunique exact-module enrollment')
    return {'format_version': 2, 'root': str(root), 'modules': modules,
            'source_hashes': {str(path): digest(root / path) for path in sorted(sources)},
            'artifact_hashes': {name: artifact_hashes(root, name) for name in modules},
            'config_hashes': {name: digest(root / name) for name in
                              ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']},
            'check_one_sha256': hashlib.sha256(CHECK_ONE.encode()).hexdigest(),
            'driver_sha256': hashlib.sha256(DRIVER.encode()).hexdigest(),
            'semantics': 'installed LeanChecker.replayFromImports; last-most-private part; empty is vacuous',
            'installed_LeanChecker_sha256': digest(prefix / 'lib/lean/LeanChecker.olean'),
            'installed_LeanChecker_source_sha256': digest(prefix / 'src/lean/LeanChecker.lean')}


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
    for relative, expected in record['evidence_hashes'].items():
        if digest(directory / relative) != expected:
            raise RuntimeError('Changed module replay evidence: ' + relative)
    resource = json.loads((directory / record['resource']).read_text())
    if resource['exit_code'] != 0 or resource['guard_failure'] is not None \
            or not resource['owned_group_gone']:
        raise RuntimeError('Module resource receipt is not a closed successful attempt')
    names = record['attempt_modules']
    counts = parse_markers((directory / record['log']).read_text(), names)
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
    basis = proof_basis(root, prefix, client)
    modules = basis['modules']
    wanted = [only] if only is not None else (list(selected) if selected is not None else modules)
    if not wanted or len(set(wanted)) != len(wanted) or not set(wanted) <= set(modules):
        raise RuntimeError('Probe contains duplicate or unenrolled exact module')
    basis_file = directory / 'basis.json'
    if basis_file.exists() and json.loads(basis_file.read_text()) != basis:
        raise RuntimeError('Replay proof basis changed; use a fresh receipt directory')
    write_json(basis_file, basis)
    if legacy is not None:
        adopt_legacy(directory, legacy, legacy_sources, legacy_runner, basis)
    completed = {}
    for name in wanted:
        path = record_path(directory, modules, name)
        if path.exists():
            record = json.loads(path.read_text())
            if record['module'] != name:
                raise RuntimeError('Receipt module identity mismatch')
            validate_record(record, directory, json_hash(basis))
            completed[name] = record
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
            if proof_basis(root, prefix, client) != basis:
                raise RuntimeError('Source/artifact/checker/config basis changed during replay')
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
                record = {'format_version': 2, 'module': name, 'status': 'passed', 'new_constants': count,
                    'semantics': 'vacuous: last most-private module part is empty' if count == 0
                    else 'installed LeanChecker.replayFromImports', 'proof_basis_sha256': json_hash(basis),
                    'attempt_modules': names, 'log': output.name, 'resource': resource_file.name,
                    'execution_profile': metadata['execution_profile'], 'evidence_hashes': evidence}
                write_json(record_path(directory, modules, name), record)
                completed[name] = record
            print(f'Kernel coverage {len(completed)}/{len(wanted)}: batch {len(names)} passed', flush=True)
        for start in range(0, len(pending), batch_size):
            check_batch(pending[start:start + batch_size])
    if proof_basis(root, prefix, client) != basis:
        raise RuntimeError('Source/artifact/checker/config basis changed after replay')
    summary = {'status': 'probe passed' if only is not None or selected is not None else 'passed',
               'expected_modules': len(modules), 'covered_modules': len(completed),
               'new_constants': sum(x['new_constants'] for x in completed.values()),
               'vacuous_modules': sum(x['new_constants'] == 0 for x in completed.values()),
               'proof_basis_sha256': json_hash(basis), 'basis': str(basis_file),
               'semantics': basis['semantics'], 'requested_batch_size': batch_size,
               'execution_profiles_preserved_per_module': True,
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
