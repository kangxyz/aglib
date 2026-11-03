#!/usr/bin/env python3
"""Tiny native CI acceptance phases, designed for separate fresh Linux jobs.

produce --transfer DIR -> upload DIR -> consume --transfer downloaded-DIR
timeout-produce --transfer DIR -> upload DIR -> timeout-resume --transfer DIR

Each phase creates its own workspace/cache, never accesses Aglib/Mathlib outputs,
and writes its commands, logs and observed results to WORK/evidence.json. Fixtures
are original source generated here; checkpoint archives never transport sources.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

CORE = Path(__file__).resolve().parents[1] / 'checkpoint.py'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Probe:
    def __init__(self, args):
        self.args = args
        self.work = args.work.absolute()
        self.work.mkdir(parents=True, exist_ok=False)
        self.root = self.work / 'workspace'; self.root.mkdir()
        self.cache = self.work / 'EMPTY-native-cache'; self.cache.mkdir()
        self.transfer = args.transfer.absolute()
        self.transfer.mkdir(parents=True, exist_ok=True)
        self.rows = []
        self.env = dict(os.environ, LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='true',
                        LAKE_RESTORE_ARTIFACTS='true', LAKE_CACHE_DIR=str(self.cache),
                        LEAN_NUM_THREADS='2')
        self.lake = args.lake
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lakefile.toml', 'name="checkpointProbe"\nenableArtifactCache=true\n'
            'restoreAllArtifacts=true\n[[require]]\nname="dep"\npath=".lake/packages/dep"\n'
            '[[lean_lib]]\nname="Native"\n[[lean_exe]]\nname="probe"\nroot="Main"\n'
            '[[lean_exe]]\nname="checker"\nroot="Checker"\n')
        self.write('.lake/packages/dep/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('.lake/packages/dep/lakefile.toml', 'name="dep"\nenableArtifactCache=true\n'
                   'restoreAllArtifacts=true\n[[lean_lib]]\nname="Dep"\n')
        self.write('.lake/packages/dep/Dep.lean', 'module\n@[expose] public def depValue : Nat := 7\n')
        self.write('Native/Good.lean', 'module\npublic import Dep\n'
                   '@[expose] public def goodValue : Nat := depValue + 1\n')
        self.write('Native.lean', 'module\npublic import Native.Good\n')
        self.write('Main.lean', 'import Native\ndef main : IO Unit := IO.println s!"value={goodValue}"\n')
        self.write('Checker.lean', 'import Native\ndef main : IO Unit := IO.println s!"checker={goodValue}"\n')
        self.run('resolve-fixture-only', ['update', '--keep-toolchain'])

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def save(self):
        (self.work / 'evidence.json').write_text(json.dumps({
            'toolchain': 'leanprover/lean4:v4.34.1', 'helper_sha256': digest(CORE),
            'phase': self.args.phase, 'commands': self.rows}, indent=2) + '\n')

    def run(self, label, arguments, expected=0, *, command=None, environment=None):
        argv = command or [self.lake, *arguments]
        log = self.work / (label + '.log')
        started = time.monotonic()
        with log.open('w') as output:
            child = subprocess.run(argv, cwd=self.root, env=environment or self.env,
                stdout=output, stderr=subprocess.STDOUT, timeout=90)
        row = {'label': label, 'argv': argv, 'exit': child.returncode,
               'seconds': time.monotonic() - started, 'log': str(log)}
        self.rows.append(row); self.save()
        if child.returncode != expected:
            raise RuntimeError(json.dumps(row) + '\n' + log.read_text())
        return log.read_text()

    def checkpoint(self, action, layer):
        path = self.transfer / (layer + '.tar.zst')
        argv = [sys.executable, str(CORE), action, '--root', str(self.root),
                '--native-cache', str(self.cache), '--layer', layer,
                '--output' if action == 'pack' else '--input', str(path)]
        return self.run(action + '-' + layer, [], command=argv)

    def no_restored_setup(self):
        paths = [str(p.relative_to(self.root)) for p in self.root.rglob('*.setup.json')
                 if p.is_file() and ('build' in p.parts and 'ir' in p.parts)]
        if paths:
            raise RuntimeError('disposable module setup files were restored: ' + repr(paths))
        self.rows.append({'label': 'no-restored-module-setup-json', 'omitted': True}); self.save()

    def artifacts(self):
        return {str(p.relative_to(self.root)): digest(p) for package in
                (self.root, self.root / '.lake/packages/dep')
                for p in (package / '.lake/build').rglob('*')
                if p.is_file() and not p.name.endswith(('.trace', '.hash', '.rsp', '.setup.json', '.ltar'))}

    def forbid_frontends(self):
        real = self.run('locate-real-lean', ['env', 'lean', '--print-prefix']).strip()
        lean = str(Path(real) / 'bin/lean')
        wrapper = self.work / 'lean-guard'
        record = self.work / 'frontend-calls.jsonl'
        wrapper.write_text('#!/usr/bin/env python3\nimport os,sys,json\na=sys.argv[1:]\n'
            'with open(' + repr(str(record)) + ',"a") as f:f.write(json.dumps(a)+"\\n")\n'
            'if a not in [["--version"],["--print-prefix"],["--githash"]]:sys.exit(91)\n'
            'os.execv(' + repr(lean) + ',[' + repr(lean) + ',*a])\n')
        wrapper.chmod(0o755)
        cc = self.work / 'cc-guard'
        cc.write_text('#!/bin/sh\necho FORBIDDEN_C_FRONTEND >&2\nexit 92\n')
        cc.chmod(0o755)
        return dict(self.env, LEAN=str(wrapper), LAKE_OVERRIDE_LEAN='true', LEAN_CC=str(cc))

    def produce(self):
        self.run('complete-build', ['build', '--rehash', 'probe', 'Native:shared',
                                   '-o', str(self.transfer / 'current-root.jsonl')])
        self.checkpoint('pack', 'dependencies')
        self.checkpoint('pack', 'root')
        # Warm only from this unpublished checkpoint. No new dependency compile.
        self.checkpoint('restore', 'dependencies')
        output = self.run('warm-build-no-new-dependency', ['build', '--no-build', '--rehash',
                                                         'probe', 'Native:shared'])
        if 'Built ' in output:
            raise RuntimeError('warm Build unexpectedly compiled')
        self.checkpoint('pack', 'dependencies')  # Complete current handoff, never an empty delta.
        self.run('prepare-checker', ['build', 'checker'])
        self.write('.lake/lint-runner/lakefile.toml', 'name="privateProbe"\nenableArtifactCache=false\n'
                   '[[lean_exe]]\nname="private"\nroot="BatchedLint"\n')
        self.write('.lake/lint-runner/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        # Same private generated source name as the accepted packaged linter.
        self.write('.lake/lint-runner/BatchedLint.lean', 'def main : IO Unit := IO.println "private-ok"\n')
        self.run('private-cache-disabled-tool', ['--dir', str(self.root / '.lake/lint-runner'),
                                               'build', 'private'])
        self.checkpoint('pack', 'tools')
        # Latest root/Test compilation is a separate generation; checker is root output.
        self.checkpoint('pack', 'root')
        self.run('stage-current-root', ['cache', 'stage', str(self.transfer / 'current-root.jsonl'),
                                       str(self.transfer / 'current-root-stage')])
        shutil.copyfile(self.work / 'evidence.json', self.transfer / 'producer-evidence.json')

    def consume(self):
        if any(self.cache.iterdir()):
            raise RuntimeError('consumer native cache must start empty')
        # Simulate every old optional restore before authoritative current overlays.
        self.checkpoint('restore', 'root')
        self.checkpoint('restore', 'tools')
        self.checkpoint('restore', 'dependencies')
        self.run('current-root-LAST', ['cache', 'unstage', str(self.transfer / 'current-root-stage'),
                                       '--force-overwrite'])
        self.no_restored_setup()
        before = self.artifacts()
        guard = self.forbid_frontends()
        self.run('no-build-cold-native-readiness', ['--no-build', '--rehash', 'build',
            'probe', 'Native:shared', 'checker'], environment=guard)
        self.run('execute-probe', ['env', str(self.root / '.lake/build/bin/probe')], environment=guard)
        self.run('execute-checker', ['env', str(self.root / '.lake/build/bin/checker')], environment=guard)
        self.run('private-tool-readiness', ['--dir', str(self.root / '.lake/lint-runner'),
            '--no-build', '--rehash', 'build', 'private'], environment=guard)
        self.run('execute-private', ['env', str(self.root / '.lake/lint-runner/.lake/build/bin/private')],
                 environment=guard)
        if before != self.artifacts():
            raise RuntimeError('readiness mutated compiled output bytes')
        self.rows.append({'label': 'compiled-artifact-byte-identity', 'files': len(before),
                          'unchanged': True, 'archive_sidecars_excluded': True}); self.save()
        self.write('Native/Good.lean', (self.root / 'Native/Good.lean').read_text() + '\n-- source drift\n')
        self.run('changed-source-rejected', ['--no-build', '--rehash', 'build', 'probe'],
                 expected=3, environment=guard)

    def slow(self):
        self.write('Native/Slow.lean', 'module\npublic import Native.Good\nmeta import Lean.Elab.Command\n'
            'run_cmd do\n  IO.FS.writeFile "slow-started" "started"\n  IO.sleep 60000\n'
            'public def slowValue : Nat := 11\n')
        self.write('Native.lean', 'module\npublic import Native.Slow\n')

    def timeout_produce(self):
        self.slow()
        marker = self.root / 'slow-started'
        log = self.work / 'interrupted-build.log'
        mapping = self.work / 'interrupted.jsonl'
        with log.open('w') as output:
            child = subprocess.Popen([self.lake, 'build', '+Native', '-o', str(mapping)],
                cwd=self.root, env=self.env, stdout=output, stderr=subprocess.STDOUT,
                start_new_session=True)
            deadline = time.monotonic() + 30
            while not marker.exists() and child.poll() is None and time.monotonic() < deadline:
                time.sleep(.05)
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGINT)
            try:
                code = child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
        if not marker.exists() or code == 0:
            raise RuntimeError('interrupt fixture did not reach unfinished Slow')
        self.rows.append({'label': 'actual-SIGINT', 'exit': code, 'log': str(log),
                          'fresh_mapping_exists': mapping.exists()}); self.save()
        # The process is dead before either scope is archived, including new Dep output.
        self.checkpoint('pack', 'root')
        self.checkpoint('pack', 'dependencies')
        self.run('salvage-is-not-pass', ['--no-build', '--rehash', 'build', '+Native',
            '-o', str(self.work / 'salvaged.jsonl')], expected=3)
        shutil.copyfile(self.work / 'evidence.json', self.transfer / 'timeout-producer-evidence.json')

    def timeout_resume(self):
        self.slow()
        self.checkpoint('restore', 'root')
        self.checkpoint('restore', 'dependencies')
        self.no_restored_setup()
        paths = [self.root / '.lake/build/lib/lean/Native/Good.olean',
                 self.root / '.lake/packages/dep/.lake/build/lib/lean/Dep.olean']
        before = [digest(p) for p in paths]
        self.run('completed-scopes-ready', ['--no-build', '--rehash', 'build', '+Native.Good'])
        # Retain the exact completed-source bytes, repair only unfinished Slow.
        text = (self.root / 'Native/Slow.lean').read_text().replace('  IO.sleep 60000\n', '')
        self.write('Native/Slow.lean', text)
        output = self.run('resume-only-unfinished', ['build', '--rehash', '+Native'])
        if 'Built Native.Good ' in output or 'Built Dep ' in output:
            raise RuntimeError('resume recompiled completed root/dependency work')
        if before != [digest(p) for p in paths]:
            raise RuntimeError('resume changed completed compiled bytes')
        if not (self.root / '.lake/build/ir/Native/Slow.setup.json').is_file():
            raise RuntimeError('unfinished module did not regenerate its setup input')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=('produce', 'consume', 'timeout-produce', 'timeout-resume'))
    parser.add_argument('--work', type=Path, required=True, help='fresh absent directory')
    parser.add_argument('--transfer', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    probe = Probe(args)
    getattr(probe, args.phase.replace('-', '_'))()
    print(json.dumps({'phase': args.phase, 'result': 'passed', 'evidence': str(probe.work / 'evidence.json')}))


if __name__ == '__main__':
    main()
