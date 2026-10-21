#!/usr/bin/env python3
"""Compile isolated guarded controls; setup failures do not count as rejection.

This leaf writes its control olean only to a temporary search-path overlay;
native Test discovery separately compiles the guarded controls normally. Each
audit source's #guard_msgs assertion requires the specific unsupported-assumption
error, and a successful guarded compilation establishes the expected rejection.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = Path('AglibTest/NegativeControls')


def main() -> int:
    environment = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT,
                                 capture_output=True, text=True)
    if environment.returncode:
        print(environment.stderr, file=sys.stderr)
        return environment.returncode
    # Lean is selected by the client's pinned toolchain in cwd; Lake supplies its
    # dependency search path once, then the isolated control view is added.
    with tempfile.TemporaryDirectory(prefix='ag-negative-controls-') as directory:
        overlay = Path(directory)
        env = dict(os.environ, LEAN_PATH=str(overlay) + os.pathsep + environment.stdout.strip())
        # Lean selects one search root per top-level namespace. Preserve positive
        # test siblings while adding the isolated fixture under AglibTest.
        cached_tests = ROOT / '.lake/build/lib/lean/AglibTest'
        for source in sorted(cached_tests.rglob('*')):
            relative = source.relative_to(cached_tests)
            if not source.is_file() or 'NegativeControls' in relative.parts:
                continue
            target = overlay / 'AglibTest' / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(source.resolve())
        fixture = CONTROLS / 'ImportedFixture.lean'
        output = overlay / fixture.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        build = subprocess.run(['lean', '-o', str(output), str(fixture)], cwd=ROOT, env=env)
        if build.returncode:
            return build.returncode
        for name, assumption in [('ImportedAudit.lean', 'importedBad'), ('LocalAudit.lean', 'localBad')]:
            result = subprocess.run(['lean', '-j2', str(CONTROLS / name)],
                                    cwd=ROOT, env=env, capture_output=True, text=True)
            combined = result.stdout + result.stderr
            if result.returncode != 0:
                print(f'Guarded negative control failed: {name}\n'
                      + f'Lean exit status: {result.returncode}\n' + combined, file=sys.stderr)
                return 1
            print(f'Guarded origin audit rejected {name}: {assumption}.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
