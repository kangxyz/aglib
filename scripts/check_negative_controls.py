#!/usr/bin/env python3
"""Replay isolated controls; compiler setup failures do not count as rejection.

The control olean uses a temporary search-path overlay. It never enters the
positive package build root or the scoped leanchecker view.
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
            if result.returncode == 0 or 'depends on unsupported assumption' not in combined \
                    or assumption not in combined:
                print(f'Negative control did not produce the required axiom rejection: {name}\n'
                      + f'Lean exit status: {result.returncode}\n' + combined, file=sys.stderr)
                return 1
            print(f'Origin audit rejected {name}: {assumption}.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
