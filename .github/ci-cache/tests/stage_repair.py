#!/usr/bin/env python3
"""Native corruption regression: warm success, cold rejection, derived-only repair."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HELPER = Path(__file__).resolve().parents[1] / 'stage.py'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--corruption', choices=('truncated', 'hash-text'), default='truncated')
    args = parser.parse_args()
    work = args.work.absolute(); work.mkdir(parents=True, exist_ok=False)
    root = work / 'producer'; root.mkdir()
    cache = work / 'native-cache'
    env = dict(os.environ, LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='true',
               LAKE_RESTORE_ARTIFACTS='true', LAKE_CACHE_DIR=str(cache))
    if Path(args.lake).is_absolute():
        env['PATH'] = str(Path(args.lake).parent) + os.pathsep + env['PATH']
    (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
    (root / 'lakefile.toml').write_text('name="StageProbe"\nenableArtifactCache=true\n'
        'restoreAllArtifacts=true\n[[lean_lib]]\nname="Probe"\n')
    (root / 'Probe.lean').write_text('module\npublic def probeValue : Nat := 7\n')
    rows = []
    def run(label, command, expected=0, cwd=root, environment=env):
        log = work / (label + '.log'); started = time.monotonic()
        with log.open('w') as output:
            process = subprocess.run(command, cwd=cwd, env=environment, text=True,
                stdout=output, stderr=subprocess.STDOUT, timeout=90)
        rows.append({'label': label, 'argv': list(map(str, command)), 'exit': process.returncode,
                     'seconds': time.monotonic() - started, 'log': str(log)})
        if process.returncode != expected:
            raise RuntimeError(json.dumps(rows[-1]) + '\n' + log.read_text())
        return log.read_text()
    mapping = work / 'valid.jsonl'
    run('valid-build', [args.lake, 'build', '--rehash', 'Probe', '-o', str(mapping)])
    prefix = Path(run('prefix', [args.lake, 'env', 'lean', '--print-prefix']).strip())
    archives = [json.loads(line) for line in mapping.read_text().splitlines()]
    dep_hash, old_archive = archives[1]
    working = root / '.lake/build/ir/Probe.ltar'
    good = working.read_bytes()
    compiled = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (root / '.lake/build').rglob('*') if p.is_file() and
        p.name.endswith(('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.ir.sig', '.c'))}
    # Keep a valid initial header, but truncate the payload. -k must not be used
    # as an integrity check: it returns success for this deliberately broken file.
    working.unlink()
    working.write_bytes(b'2cef175a2d92a431' if args.corruption == 'hash-text' else
                        good[:max(32, len(good) // 2)])
    hash_source = work / 'HashArchive.lean'
    hash_source.write_text('import Lake\nopen Lake\ndef main (args : List String) : IO Unit := do\n'
                          '  IO.println (← computeFileHash args.head!)\n')
    bad_hash = run('native-hash', [str(prefix / 'bin/lean'), '--run', str(hash_source), str(working)]).strip()
    bad_name = bad_hash + '.ltar'
    artifact = cache / 'artifacts' / bad_name; artifact.write_bytes(working.read_bytes())
    bad_mapping = work / 'bad.jsonl'
    bad_mapping.write_text(json.dumps(archives[0]) + '\n' + json.dumps([dep_hash, bad_name]) + '\n')
    run('register-derived-only-bad-map', [args.lake, 'cache', 'add', str(bad_mapping)])
    warm_mapping = work / 'warm-export.jsonl'
    run('warm-export-still-succeeds', [args.lake, '--no-build', '--rehash', 'build', 'Probe', '-o', str(warm_mapping)])
    bad_stage = work / 'bad-stage'
    run('bad-stage-copy-succeeds', [args.lake, 'cache', 'stage', str(warm_mapping), str(bad_stage)])
    run('comments-only-is-insufficient', [str(prefix / 'bin/leantar'), '-k', str(bad_stage / bad_name)],
        expected=1 if args.corruption == 'hash-text' else 0)
    run('full-verify-rejects', [sys.executable, str(HELPER), 'verify', '--root', str(root),
        '--staging', str(bad_stage), '--report', str(work / 'bad-verify.json')], expected=1)
    if not (bad_stage / bad_name).is_file():
        raise RuntimeError('pure verify mutated its original stage input')
    repaired = work / 'repaired-stage'; report = work / 'repair-report.json'
    run('selective-repair', [sys.executable, str(HELPER), 'prepare', '--root', str(root),
        '--mapping', str(warm_mapping), '--staging', str(repaired), '--native-cache', str(cache),
        '--build-target', 'Probe', '--report', str(report)])
    data = json.loads(report.read_text())
    if not data['success'] or data['first']['bad_archives'] != [bad_name] or data['final']['bad_archives']:
        raise RuntimeError('selective repair did not close the corrupted transport')
    if any(hashlib.sha256(Path(p).read_bytes()).hexdigest() != h for p, h in compiled.items()):
        raise RuntimeError('repair changed valid compiled outputs')
    cold = work / 'consumer'; cold.mkdir()
    for name in ('lean-toolchain', 'lakefile.toml', 'Probe.lean'):
        shutil.copyfile(root / name, cold / name)
    fresh = dict(env, LAKE_CACHE_DIR=str(work / 'EMPTY-consumer-cache'))
    run('cold-unstage', [args.lake, 'cache', 'unstage', str(repaired), '--force-overwrite'], cwd=cold, environment=fresh)
    run('cold-no-build-readiness', [args.lake, '--no-build', '--rehash', 'build', 'Probe'], cwd=cold, environment=fresh)
    (work / 'evidence.json').write_text(json.dumps({'helper_sha256': hashlib.sha256(HELPER.read_bytes()).hexdigest(),
        'corruption': args.corruption, 'bad_archive': bad_name,
        'commands': rows, 'compiled_bytes_unchanged': True, 'repair_report': str(report)}, indent=2) + '\n')
    print(json.dumps({'result': 'passed', 'evidence': str(work / 'evidence.json')}))


if __name__ == '__main__':
    main()
