#!/usr/bin/env python3
"""Replay exact current modules sequentially through installed LeanChecker semantics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from check_compiled_inventory import check_inventory
from library_sources import source_modules, test_modules, module_name, module_path
from resource_guard import run, frontend_args, limits
from run_style_linter import lake_environment

ROOT = Path(__file__).resolve().parents[1]
DRIVER = '''import LeanChecker

open Lean

-- Deliberately evaluated as a command: the imported fanout main is never run.
#eval do
  initSearchPath (← findSysroot)
  let some text ← IO.getEnv "AGLIB_KERNEL_MODULE"
    | throw <| IO.userError "missing exact module identity"
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
    IO.println s!"AGLIB_KERNEL_CHECKED {text} {count}"
'''


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


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


def replay(root, directory, only=None, client=False):
    root = root.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    if not client:
        errors = check_inventory(root)
        if errors:
            raise RuntimeError('\n'.join(errors))
    sources = expected_sources(root, client)
    if client:
        library = root / '.lake/build/lib/lean'
        actual = {path.relative_to(library).with_suffix('.lean')
                  for path in (library / 'Consumer').rglob('*.olean')}
        if (library / 'Consumer.olean').is_file():
            actual.add(Path('Consumer.lean'))
        if actual != sources:
            raise RuntimeError('Independent client compiled inventory differs from current source')
    modules = sorted(module_name(path) for path in sources)
    if len(set(modules)) != len(sources):
        raise RuntimeError('Nonunique exact-module enrollment')
    if only is not None and only not in modules:
        raise RuntimeError('Probe target is not enrolled: ' + only)
    environment = dict(lake_environment(root))
    lean = environment.pop('lean')
    prefix = Path(subprocess.check_output([lean, '--print-prefix'], text=True).strip())
    if not (prefix / 'lib/lean/LeanChecker.olean').is_file():
        raise RuntimeError('Installed LeanChecker module is required')
    budget = limits()
    basis = {'root': str(root), 'modules': modules,
             'source_hashes': {str(path): digest(root / path) for path in sorted(sources)},
             'artifact_hashes': {name: artifact_hashes(root, name) for name in modules},
             'config_hashes': {name: digest(root / name) for name in
                               ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']},
             'driver_sha256': hashlib.sha256(DRIVER.encode()).hexdigest(),
             'installed_LeanChecker_sha256': digest(prefix / 'lib/lean/LeanChecker.olean'),
             'installed_LeanChecker_source_sha256': digest(prefix / 'src/lean/LeanChecker.lean'),
             'limits': budget}
    basis_file = directory / 'basis.json'
    if basis_file.exists() and json.loads(basis_file.read_text()) != basis:
        raise RuntimeError('Replay basis changed; use a fresh receipt directory')
    basis_file.write_text(json.dumps(basis, indent=2) + '\n')
    completed = []
    with tempfile.TemporaryDirectory(prefix='aglib-kernel-') as temporary:
        driver = Path(temporary) / 'CheckOne.lean'
        driver.write_text(DRIVER)
        for index, name in enumerate(modules):
            if only is not None and name != only:
                continue
            entry = directory / ('module-' + str(index).zfill(4) + '.json')
            if entry.is_file():
                saved = json.loads(entry.read_text())
                if saved['module'] == name and saved['status'] == 'passed':
                    completed.append(saved)
                    continue
                raise RuntimeError('Existing incomplete module receipt: ' + str(entry))
            output = directory / ('module-' + str(index).zfill(4) + '.log')
            env = dict(os.environ, **environment, AGLIB_KERNEL_MODULE=name, LEAN_NUM_THREADS='1',
                       LEAN_SYSROOT=str(prefix))
            # No --run: imported LeanChecker.main must never be selected.
            command = frontend_args(lean) + [str(driver)]
            # Logs are opened by a tiny Python redirection wrapper outside the guard;
            # the guard itself and all child Lean processes remain in this owner group.
            with output.open('w') as log:
                # Popen inherits file descriptors, so use explicit descriptor redirection.
                saved_out, saved_err = os.dup(1), os.dup(2)
                try:
                    os.dup2(log.fileno(), 1); os.dup2(log.fileno(), 2)
                    code = run(command, cwd=root, env=env,
                               receipt=directory / ('resource-' + str(index).zfill(4) + '.json'))
                finally:
                    os.dup2(saved_out, 1); os.dup2(saved_err, 2)
                    os.close(saved_out); os.close(saved_err)
            marker = 'AGLIB_KERNEL_CHECKED ' + name + ' '
            matches = [line for line in output.read_text().splitlines() if line.startswith(marker)]
            if code or len(matches) != 1:
                raise RuntimeError(f'Exact module {name} failed ({code}); inspect {output}')
            count = int(matches[0][len(marker):])
            saved = {'module': name, 'status': 'passed', 'new_constants': count,
                     'semantics': 'vacuous: last most-private module part is empty' if count == 0
                     else 'installed LeanChecker.replayFromImports', 'log': str(output)}
            entry.write_text(json.dumps(saved, indent=2) + '\n')
            completed.append(saved)
            print(f'Kernel {index + 1}/{len(modules)}: {name} ({count} new constants)', flush=True)
    if {name: artifact_hashes(root, name) for name in modules} != basis['artifact_hashes'] or any(
            digest(root / path) != sha for path, sha in basis['source_hashes'].items()):
        raise RuntimeError('Source/artifact basis changed during replay')
    summary = {'status': 'probe passed' if only else 'passed', 'expected_modules': len(modules),
               'covered_modules': len(completed), 'new_constants': sum(x['new_constants'] for x in completed),
               'vacuous_modules': sum(x['new_constants'] == 0 for x in completed),
               'basis': str(basis_file), 'limits': budget}
    (directory / ('probe.json' if only else 'coverage.json')).write_text(
        json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--receipt-dir', type=Path, required=True)
    parser.add_argument('--only', help='one enrolled probe target; cannot claim full coverage')
    parser.add_argument('--client', action='store_true')
    args = parser.parse_args()
    try:
        replay(args.root, args.receipt_dir, args.only, args.client)
        return 0
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print('Bounded kernel replay failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
