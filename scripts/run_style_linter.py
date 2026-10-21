#!/usr/bin/env python3
"""Run pinned Mathlib style checks with an isolated optional-dependency overlay.

The exact driver and, if missing, Cli.Basic and ImportGraph.Imports.FromSource
are compiled into a temporary directory, never an immutable dependency cache.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from library_sources import lean_imports, module_path

ROOT = Path(__file__).resolve().parents[1]
DRIVER = Path('.lake/packages/mathlib/scripts/lint-style.lean')
OPTIONAL = {
    'Cli.Basic': Path('.lake/packages/Cli'),
    'ImportGraph.Imports.FromSource': Path('.lake/packages/importGraph'),
}


def search_roots(root: Path, sysroot: Path) -> list[Path]:
    return [root / '.lake/build/lib/lean'] + [
        package / '.lake/build/lib/lean'
        for package in sorted((root / '.lake/packages').iterdir()) if package.is_dir()
    ] + [sysroot / 'lib/lean']


def cached_module(name: str, search: list[Path]) -> Path | None:
    relative = module_path(name).with_suffix('.olean')
    return next((base / relative for base in search if (base / relative).is_file()), None)


def plan_runtime(root: Path, sysroot: Path) -> dict:
    """Inspect direct driver imports and exact optional-source prerequisites read-only."""
    search = search_roots(root, sysroot)
    required = lean_imports((root / DRIVER).read_text())
    cached, compile_modules, missing = [], [], []
    for name in required:
        artifact = cached_module(name, search)
        if artifact:
            cached.append({'module': name, 'olean': str(artifact)})
            continue
        if name not in OPTIONAL:
            missing.append(name)
            continue
        source = root / OPTIONAL[name] / module_path(name)
        if not source.is_file():
            missing.append(name + ' (source unavailable)')
            continue
        for imported in lean_imports(source.read_text()):
            if cached_module(imported, search) is None:
                missing.append(imported + ' (optional-source prerequisite)')
        compile_modules.append({'module': name, 'source': str(source),
                                'package_root': str(root / OPTIONAL[name])})
    lake_shared = next((path for path in [
        sysroot / 'lib/lean/libLake_shared.dylib',
        sysroot / 'lib/lean/libLake_shared.so',
        sysroot / 'bin/libLake_shared.dll',
    ] if path.is_file()), None)
    if lake_shared is None:
        missing.append('pinned Lake shared library')
    return {'driver': str(root / DRIVER), 'lake_shared_library': str(lake_shared),
            'cached_direct_imports': cached,
            'isolated_compile_modules': compile_modules, 'missing_prerequisites': sorted(set(missing)),
            'namespace_cache_roots': {
                name: [str(base / name) for base in search if (base / name).is_dir()]
                for name in sorted({entry['module'].split('.')[0] for entry in compile_modules})
            },
            'boundary': 'Direct import/source prerequisite inspection; runtime replay is separate.'}


def seed_cached_namespaces(overlay: Path, plan: dict) -> None:
    """Preserve cached namespace siblings when Lean selects the overlay's module root."""
    for namespace, roots in plan['namespace_cache_roots'].items():
        for cached in map(Path, roots):
            for source in sorted(cached.rglob('*')):
                if not source.is_file():
                    continue
                target = overlay / namespace / source.relative_to(cached)
                if target.exists():
                    continue
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(source.resolve())


def lake_environment(root: Path) -> dict:
    # Project only these nonsecret variables from Lake's pinned execution environment.
    selected_lean = os.environ.get('LEAN')
    query = ('import json,os,shutil; print(json.dumps({'
             '"lean":os.environ.get("LEAN") or shutil.which("lean"),"LEAN_PATH":os.environ.get("LEAN_PATH",""),'
             '"LEAN_SRC_PATH":os.environ.get("LEAN_SRC_PATH","")}))')
    result = subprocess.run(['lake', 'env', 'python3', '-c', query], cwd=root,
                            capture_output=True, text=True, check=True)
    environment = json.loads(result.stdout)
    # Lake can replace LEAN while constructing its environment. Keep the outer
    # owned compiler wrapper, including its native memory/thread caps.
    if selected_lean:
        environment['lean'] = selected_lean
    if not environment['lean']:
        raise RuntimeError('Lake environment did not identify the pinned Lean executable')
    return environment


def selected_driver(source: str) -> str:
    """Retain pinned options/checks; replace only the umbrella import enumeration."""
    start = source.index('  -- Get all the imports, but only those in the same package.')
    end = source.index('  -- Read the `nolints` file', start)
    return source[:start] + '  Lean.initSearchPath (← Lean.findSysroot)\n  let allModuleNames := originModules\n\n' + source[end:]


def run(root: Path, modules: list[str] | None = None) -> int:
    environment = lake_environment(root)
    lean = environment.pop('lean')
    prefix = subprocess.run([lean, '--print-prefix'], cwd=root, capture_output=True,
                            text=True, check=True).stdout.strip()
    plan = plan_runtime(root, Path(prefix))
    if plan['missing_prerequisites']:
        raise RuntimeError('Missing cached style-runtime prerequisites: '
                           + ', '.join(plan['missing_prerequisites']))
    # Compile only the exact driver and two optional modules into an isolated overlay.
    # The imported IR/olean parts emitted by -o remain beside that output path.
    with tempfile.TemporaryDirectory(prefix='aglib-style-runtime-') as directory:
        overlay = Path(directory)
        seed_cached_namespaces(overlay, plan)
        env = dict(os.environ, **environment)
        env['LEAN_PATH'] = str(overlay) + os.pathsep + environment['LEAN_PATH']
        for entry in plan['isolated_compile_modules']:
            relative = module_path(entry['module'])
            output = overlay / relative.with_suffix('.olean')
            if output.exists() or output.is_symlink():
                raise RuntimeError('Optional output would overwrite a cached artifact: ' + str(output))
            output.parent.mkdir(parents=True, exist_ok=True)
            result = subprocess.run([lean, '-o', str(output), relative.as_posix()],
                                    cwd=entry['package_root'], env=env)
            if result.returncode:
                return result.returncode
        # Importing the compiled driver initializes its option declarations before main.
        # Running its source directly cannot evaluate a same-module [init] declaration.
        driver = overlay / 'AglibStyleDriver.lean'
        source = (root / DRIVER).read_text()
        driver.write_text(selected_driver(source) if modules else source)
        result = subprocess.run([lean, '-o', str(driver.with_suffix('.olean')), driver.name],
                                cwd=overlay, env=env)
        if result.returncode:
            return result.returncode
        shim = overlay / 'RunStyle.lean'
        shim.write_text('import AglibStyleDriver\n')
        # These are the exact pinned driver bytes and arguments. --fix is absent.
        return subprocess.run([lean, '--load-dynlib', plan['lake_shared_library'],
                               '--run', str(shim), *(modules or ['Aglib', 'AglibTest'])],
                              cwd=root, env=env).returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-prerequisites', action='store_true',
                        help='read-only readiness inspection; does not invoke Lake or compile')
    parser.add_argument('--sysroot', type=Path,
                        help='installed pinned Lean prefix for read-only inspection')
    parser.add_argument('--modules', nargs='+', help='exact source modules; preserves all pinned style checks')
    args = parser.parse_args()
    try:
        if args.check_prerequisites:
            if args.sysroot is None:
                parser.error('--check-prerequisites requires --sysroot')
            plan = plan_runtime(ROOT, args.sysroot)
            print(json.dumps(plan, indent=2))
            return 1 if plan['missing_prerequisites'] else 0
        if args.sysroot is not None:
            parser.error('--sysroot is only used with --check-prerequisites')
        return run(ROOT, args.modules)
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f'Style runtime failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
