#!/usr/bin/env python3
"""Build local targets in dependency order, with one capped compiler at a time."""
import argparse
from contextlib import contextmanager
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from library_sources import lean_imports, module_path
from resource_guard import limits, run


def build_threads(environment=None):
    environment = os.environ if environment is None else environment
    threads = int(environment.get('AGLIB_BUILD_THREADS', environment.get('LEAN_NUM_THREADS', '1')))
    available = os.cpu_count() or 1
    if not 1 <= threads <= available:
        raise ValueError('Build threads must be positive and not exceed available logical CPUs')
    return threads


@contextmanager
def capped_toolchain(root, threads=1):
    # Elan's read-only locator does not launch an unguarded Lean frontend.
    lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=root, text=True).strip()
    prefix = Path(lean).parent.parent
    budget = limits()
    with tempfile.TemporaryDirectory(prefix='aglib-capped-toolchain-') as temporary:
        overlay = Path(temporary)
        for entry in prefix.iterdir():
            if entry.name != 'bin':
                (overlay / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
        (overlay / 'bin').mkdir()
        for entry in (prefix / 'bin').iterdir():
            if entry.name != 'lean':
                (overlay / 'bin' / entry.name).symlink_to(entry)
        wrapper = overlay / 'bin/lean'
        wrapper.write_text('#!/usr/bin/env python3\nimport os,sys\n'
            'args=[]; i=1\nwhile i<len(sys.argv):\n'
            ' a=sys.argv[i]\n'
            ' if a in ["-j","-M"]: i+=2; continue\n'
            ' if a.startswith("-j") or a.startswith("-M"): i+=1; continue\n'
            ' args.append(a); i+=1\n'
            'threads=1 if args in [["--githash"],["--print-prefix"],["--version"]] else '
            + repr(threads) + '\n'
            'os.environ["LEAN_NUM_THREADS"]=str(threads)\n'
            'os.execv(' + repr(lean) + ',[' + repr(lean) + ',"-j"+str(threads),'
            + repr('-M' + str(budget['lean_memory_mb'])) + ']+args)\n')
        wrapper.chmod(0o755)
        yield dict(os.environ, LEAN_SYSROOT=str(overlay), LEAN=str(wrapper),
                   LAKE_OVERRIDE_LEAN='true', LEAN_NUM_THREADS='1',
                   PATH=str(overlay / 'bin') + os.pathsep + os.environ.get('PATH', ''))


def source_order(root, targets):
    seen, active, result = set(), set(), []
    def visit(name):
        if name in seen:
            return
        if name in active:
            raise ValueError('Local import cycle: ' + name)
        path = root / module_path(name)
        if not path.is_file():
            raise ValueError('Missing local build target: ' + name)
        active.add(name)
        for dependency in lean_imports(path.read_text()):
            if (root / module_path(dependency)).is_file():
                visit(dependency)
        active.remove(name); seen.add(name); result.append(name)
    for target in targets:
        visit(target)
    return result


def expected_cache_miss(code, output):
    # Pinned Lake Build/Run.lean assigns noBuildCode = 3. A mixed graph can
    # contain other failures too, so never classify by exit status alone.
    errors = [line.split('error:', 1)[1].strip()
              for line in output.splitlines() if 'error:' in line]
    return code == 3 and bool(errors) and all(
        error == 'target is out-of-date and needs to be rebuilt' for error in errors)


def build(root, targets, directory, rehash=False):
    directory.mkdir(parents=True, exist_ok=True)
    source_order(root, targets)
    lake = ['lake'] + (['--rehash'] if rehash else [])
    budget = limits()
    # Lake's one worker admits one external frontend at a time. Its compiler
    # wrapper supplies the requested native parallelism only to that child.
    # The strict guard remains a fail-closed check on actual process concurrency.
    budget['native_build_threads'] = build_threads()
    with capped_toolchain(root, threads=budget['native_build_threads']) as env:
        log = directory / 'cached-check.log'
        # Each receipt directory owns one probe. Preserve earlier evidence rather
        # than silently overwriting it when a caller accidentally reuses a path.
        with log.open('x') as output:
            code = run(lake + ['--no-build', 'build', *targets], cwd=root, env=env,
                       receipt=directory / 'cached-check.json', budget=budget,
                       stdout=output, stderr=output)
        if code == 0:
            print(f'Build cache hit; no compilation needed (probe log: {log}).', flush=True)
            return 0
        diagnostics = log.read_text()
        if not expected_cache_miss(code, diagnostics):
            print(f'Build cache probe failed ({code}); see {log}.', file=sys.stderr, flush=True)
            print(diagnostics, file=sys.stderr, end='' if diagnostics.endswith('\n') else '\n')
            return code
        print(f'Build cache miss; building requested targets (probe log: {log}).', flush=True)
        return run(lake + ['build', *targets], cwd=root, env=env,
                   receipt=directory / 'graph-build.json', budget=budget)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--receipt-dir', type=Path, required=True)
    parser.add_argument('--rehash', action='store_true')
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args()
    try:
        return build(args.root.resolve(), args.targets, args.receipt_dir, args.rehash)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print('Serial build failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
