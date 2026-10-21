"""Common finite native checks with canonical isolated defining-origin environments.

The declaration batch shares Lean's persistent ImportState prefix, not an environment
containing the union of its targets. All generated outputs belong to a temporary overlay.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from ..project.source import IDENT, MODULE, module_path
import re


def module_components(module: str) -> list[str]:
    if MODULE.fullmatch(module) is None:
        raise ValueError(f"Invalid Lean module name: {module}")
    return [p[1:-1] if p.startswith("«") else p for p in re.findall(IDENT, module)]

BATCH_SIZE = 8
KINDS = ('source', 'style', 'declarations', 'builtin', 'axioms', 'inventory', 'controls', 'expected-failure')


def assets_directory() -> Path:
    return Path(__file__).with_name('lean')


def checker_inputs(kind: str, root: Path | None = None, config: Path | None = None) -> tuple[Path, ...]:
    """Checker source inputs; consumer closure binding adds native imports and policy data."""
    paths = [Path(__file__), Path(__file__).resolve().parents[1] / 'project/source.py']
    if kind in ('declarations', 'axioms', 'inventory', 'controls'):
        paths.append(assets_directory() / 'Native.lean')
    if kind == 'controls':
        paths.extend(sorted((assets_directory() / 'Controls').glob('*.lean')))
    if kind == 'declarations' and root is not None:
        paths.extend(_nolint_paths(root, config))
    if kind == 'style':
        paths.append(Path(__file__).with_name('text_style.py'))
    if kind == 'style' and root is not None:
        paths.extend(root / '.lake/packages/mathlib/scripts' / name for name in ('lint-style.lean', 'lint-style.py'))
        paths.extend(p for p in (root / 'scripts/nolints-style.txt', root / 'lakefile.toml', root / 'lakefile.lean') if p.is_file())
    if kind in ('source', 'builtin', 'controls'):
        paths.append(Path(__file__).with_name('guards.py'))
    if config is not None:
        paths.append(Path(config))
    return tuple(paths)


def runtime_roots(kind: str) -> tuple[str, ...]:
    if kind in ('declarations', 'axioms', 'inventory', 'controls'):
        return ('Lean.Util.CollectAxioms', 'Lean.Data.Json.Parser', 'Batteries.Tactic.Lint')
    if kind == 'style':
        return ('Lake.CLI.Main', 'Lean.Elab.ParseImportsFast', 'Batteries.Data.String.Basic',
                'Mathlib.Tactic.Linter.TextBased', 'Cli.Basic', 'ImportGraph.Imports.FromSource')
    return ()


def runtime_source_roots(kind: str) -> tuple[str, ...]:
    """Exact optional support sources whose absent outputs have an isolated fallback."""
    return ('Cli.Basic', 'ImportGraph.Imports.FromSource') if kind == 'style' else ()


def _config_data(config: Path) -> dict:
    """Read the raw shared schema; semantic enrollment remains load_config's owner."""
    if config.suffix == '.json':
        def unique_object(pairs):
            result = {}
            for key, value in pairs:
                if key in result:
                    raise ValueError(f'Duplicate JSON configuration key: {key}')
                result[key] = value
            return result
        data = json.loads(config.read_text(), object_pairs_hook=unique_object)
    else:
        import tomllib
        data = tomllib.loads(config.read_text())
    if not isinstance(data, dict) or not isinstance(data.get('policy', {}), dict):
        raise ValueError('Native configuration and policy must be objects')
    return data


def _validate_native_policy(kind: str, config: Path | None) -> None:
    if config is None or kind not in ('axioms', 'inventory', 'controls'):
        return
    policy = _config_data(config).get('policy', {})
    for key in (('axioms', 'private_generated') if kind in ('axioms', 'controls') else ('private_generated',)):
        if policy.get(key):
            raise ValueError(f'Unsupported nonempty policy.{key}: common native checks use the fixed standard axiom/private-generated policy')


def emit(record: dict) -> None:
    print(json.dumps(record, separators=(',', ':')), flush=True)


def _emit_origin(record: dict, metadata: dict | None, results_jsonl: Path | None) -> None:
    record = dict(record)
    record.setdefault('completed', True)
    if metadata is not None:
        if metadata.get('kind') is not None and record.get('kind') != metadata['kind']:
            raise ValueError('Native result kind does not match its batch selection')
        key = tuple(module_components(record['module']))
        item = metadata['items'].get(key)
        if item is None:
            raise ValueError('Native runtime reported an unselected origin')
        record.update({key: item[key] for key in ('id', 'module', 'input_key')})
        record['invocation'] = metadata['invocation']
    if results_jsonl is not None:
        with results_jsonl.open('a') as output:
            output.write(json.dumps(record, separators=(',', ':')) + '\n')
            output.flush()
    emit(record)


def _nolint_paths(root: Path, config: Path | None = None) -> list[Path]:
    paths = [root / 'scripts/nolints.json'] if (root / 'scripts/nolints.json').is_file() else []
    if config is not None:
        config = config.resolve()
        data = _config_data(config)
        if config.parent.name in ('.github', '.lean-ci'):
            repository = config.parent.parent
        else:
            found = subprocess.run(['git', 'rev-parse', '--show-toplevel'], cwd=root,
                                   capture_output=True, text=True, check=True)
            repository = Path(found.stdout.strip()).resolve()
        values = data.get('policy', {}).get('nolints', [])
        if not isinstance(values, list) or not all(isinstance(p, str) for p in values):
            raise ValueError('policy.nolints must contain data file paths')
        for value in values:
            path = (repository / value).resolve()
            if not path.is_relative_to(repository) or not path.is_file():
                raise ValueError('nolints data path escapes repository or is missing')
            if path not in paths:
                paths.append(path)
    return paths


def _nolints(root: Path, config: Path | None = None) -> list:
    result = []
    for path in _nolint_paths(root, config):
        entries = json.loads(path.read_text())
        if not isinstance(entries, list) or not all(isinstance(p, list) and len(p) == 2
                and all(isinstance(name, str) and name for name in p) for p in entries):
            raise ValueError(f'Invalid Batteries nolints data: {path}')
        result.extend(entries)
    return result


def lake_environment(root: Path) -> dict[str, str]:
    query = ('import json,os,shutil; print(json.dumps({'
             '"lean":os.environ.get("LEAN") or shutil.which("lean"),'
             '"LEAN_PATH":os.environ.get("LEAN_PATH",""),'
             '"LEAN_SRC_PATH":os.environ.get("LEAN_SRC_PATH","")}))')
    result = subprocess.run(['lake', 'env', 'python3', '-P', '-c', query], cwd=root,
                            capture_output=True, text=True, check=True)
    environment = json.loads(result.stdout)
    if os.environ.get('LEAN'):
        environment['lean'] = os.environ['LEAN']
    if not environment.get('lean'):
        raise RuntimeError('Lake did not identify its Lean executable')
    environment['LEAN_SYSROOT'] = subprocess.run([environment['lean'], '--print-prefix'], cwd=root, capture_output=True, text=True, check=True).stdout.strip()
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH'):
        environment[key] = os.pathsep.join(str(Path(p) if Path(p).is_absolute() else root / p)
                                            for p in environment.get(key, '').split(os.pathsep) if p)
    return environment


def _compile(lean: str, source: Path, output: Path, cwd: Path, env: dict) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run([lean, '-o', str(output), str(source)], cwd=cwd, env=env, check=True)


def run_origins(kind: str, root: Path, components: list[list[str]], *,
                environment: dict | None = None, pilot: bool = False,
                metadata: dict | None = None, results_jsonl: Path | None = None,
                config_path: Path | None = None) -> int:
    if not components:
        raise ValueError('Native origin checks require a nonempty exact selection')
    environment = dict(environment or lake_environment(root))
    lean = environment.pop('lean')
    failed = False
    with tempfile.TemporaryDirectory(prefix='lean-ci-native-') as directory:
        overlay = Path(directory)
        env = dict(os.environ, **environment)
        env['LEAN_PATH'] = str(overlay) + os.pathsep + environment.get('LEAN_PATH', '')
        # Compilation imports only the shared runtime, never a subject or umbrella.
        driver = overlay / 'LeanCiNativeDriver.lean'
        driver.write_text((assets_directory() / 'Native.lean').read_text())
        _compile(lean, driver, overlay / 'LeanCiNativeDriver.olean', overlay, env)
        shim = overlay / 'Run.lean'
        shim.write_text('import LeanCiNativeDriver\n')
        for start in range(0, len(components), BATCH_SIZE):
            selected = components[start:start + BATCH_SIZE]
            process = subprocess.Popen([lean, '--run', str(shim), kind, json.dumps(selected),
                                        str(pilot).lower(), json.dumps(_nolints(root, config_path)) if kind in ('declarations', 'reference') else '[]'], cwd=root, env=env,
                                       stdout=subprocess.PIPE, text=True)
            seen: set[str] = set()
            assert process.stdout is not None
            for line in process.stdout:
                # Preserve native diagnostics, forwarding successful peer records immediately.
                try:
                    record = json.loads(line)
                except json.JSONDecodeError:
                    print(line, end='', file=sys.stderr, flush=True)
                    continue
                if not isinstance(record, dict) or 'module' not in record:
                    print(line, end='', file=sys.stderr, flush=True)
                    continue
                if record.get('kind') != ('declarations' if kind == 'reference' else kind):
                    process.stdout.close()
                    process.terminate()
                    process.wait()
                    raise ValueError('Native result kind does not match requested check')
                seen.add(record['module'])
                failed |= not record.get('success', False)
                _emit_origin(record, metadata, results_jsonl)
            process.stdout.close()
            failed |= process.wait() != 0
            for name in selected:
                display = '.'.join(('«' + c + '»') if '.' in c or ' ' in c else c for c in name)
                if display not in seen:
                    failed = True
                    _emit_origin({'kind': kind, 'module': display, 'success': False, 'completed': False,
                          'error': 'Native process ended before reporting this origin'}, metadata, results_jsonl)
    return int(failed)


def run_expected_failure(root: Path, sources: list[Path], environment: dict | None = None) -> int:
    if not sources:
        raise ValueError('Expected-failure requires named fixture paths')
    environment = dict(environment or lake_environment(root))
    lean = environment.pop('lean')
    env = dict(os.environ, **environment)
    failed = False
    for source in sources:
        path = source if source.is_absolute() else root / source
        path = path.resolve()
        if not path.is_file() or path.suffix != '.lean':
            raise ValueError(f'Expected-failure fixture is not a Lean source: {source}')
        result = subprocess.run([lean, path.name], cwd=path.parent, env=env, capture_output=True, text=True)
        # Signals, absent dependencies and tool startup errors cannot establish a negative control.
        output = result.stdout + result.stderr
        success = (result.returncode > 0 and ': error' in output and
                   not any(text in output for text in ('object file ', 'unknown module prefix',
                                                       'does not exist', 'failed to open file')))
        failed |= not success
        emit({'kind': 'expected-failure', 'module': str(source), 'success': success,
              'exit_code': result.returncode, 'diagnostics': output})
    return int(failed)


def _style_source(source: str) -> str:
    start = source.index('  -- Get all the imports, but only those in the same package.')
    end = source.index('  -- Read the `nolints` file', start)
    return source[:start] + '  Lean.initSearchPath (← Lean.findSysroot)\n  let allModuleNames := originModules\n\n' + source[end:]


def run_style(root: Path, modules: list[str], environment: dict | None = None) -> int:
    """Pinned Python text rules, then Lean style, using exact sources and isolated support."""
    from ..project.source import lean_imports
    if not modules:
        raise ValueError('Style requires a nonempty exact source selection')
    sources = [root / module_path(module) for module in modules]
    for module, source in zip(modules, sources):
        if not source.is_file():
            raise ValueError(f'Missing selected style source: {module}')
    from . import text_style
    code = text_style.run(root / '.lake/packages/mathlib/scripts/lint-style.py', sources)
    if code:
        for module in modules:
            emit({'kind': 'style', 'module': module, 'success': False, 'stage': 'python-text'})
        return code
    environment = dict(environment or lake_environment(root))
    lean = environment.pop('lean')
    sysroot = Path(subprocess.run([lean, '--print-prefix'], cwd=root, text=True,
                                 capture_output=True, check=True).stdout.strip())
    packages = root / '.lake/packages'
    search = [root / '.lake/build/lib/lean'] + [
        p / '.lake/build/lib/lean' for p in sorted(packages.iterdir()) if p.is_dir()
    ] + [sysroot / 'lib/lean']
    optional = {'Cli.Basic': packages / 'Cli',
                'ImportGraph.Imports.FromSource': packages / 'importGraph'}
    def cached(name):
        return next((p / module_path(name).with_suffix('.olean') for p in search
                     if (p / module_path(name).with_suffix('.olean')).is_file()), None)
    driver_source = (packages / 'mathlib/scripts/lint-style.lean').read_text()
    missing, compile_modules = [], []
    for module in lean_imports(driver_source):
        if cached(module):
            continue
        if module not in optional:
            missing.append(module)
            continue
        source = optional[module] / module_path(module)
        if not source.is_file():
            missing.append(module)
            continue
        missing.extend(name for name in lean_imports(source.read_text()) if not cached(name))
        compile_modules.append((module, source, optional[module]))
    if missing:
        raise RuntimeError('Missing cached style runtime prerequisites: ' + ', '.join(sorted(set(missing))))
    shared = next((p for p in [sysroot / 'lib/lean/libLake_shared.dylib',
                             sysroot / 'lib/lean/libLake_shared.so', sysroot / 'bin/libLake_shared.dll']
                   if p.is_file()), None)
    if shared is None:
        raise RuntimeError('Missing pinned Lake shared library')
    with tempfile.TemporaryDirectory(prefix='lean-ci-style-') as directory:
        overlay = Path(directory)
        # Lean chooses a namespace root, so retain cached siblings for optional source overlays.
        for namespace in {m.split('.')[0] for m, _, _ in compile_modules}:
            for base in search:
                cached_root = base / namespace
                if not cached_root.is_dir():
                    continue
                for source in cached_root.rglob('*'):
                    target = overlay / namespace / source.relative_to(cached_root)
                    if source.is_file() and not target.exists():
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.symlink_to(source.resolve())
        env = dict(os.environ, **environment)
        env['LEAN_PATH'] = str(overlay) + os.pathsep + environment.get('LEAN_PATH', '')
        for module, source, package in compile_modules:
            _compile(lean, source.relative_to(package), overlay / module_path(module).with_suffix('.olean'), package, env)
        driver = overlay / 'LeanCiStyleDriver.lean'
        driver.write_text(_style_source(driver_source))
        _compile(lean, driver, driver.with_suffix('.olean'), overlay, env)
        shim = overlay / 'RunStyle.lean'
        shim.write_text('import LeanCiStyleDriver\n')
        result = subprocess.run([lean, '--load-dynlib', str(shared), '--run', str(shim), *modules],
                                cwd=root, env=env)
        for module in modules:
            emit({'kind': 'style', 'module': module, 'success': result.returncode == 0})
        return result.returncode


def run_native_controls(root: Path, environment: dict | None = None) -> int:
    """Named common positive inventory and negative private-axiom controls."""
    import contextlib
    import io
    environment = dict(environment or lake_environment(root))
    lean = environment['lean']
    with tempfile.TemporaryDirectory(prefix='lean-ci-controls-') as directory:
        overlay = Path(directory)
        env = dict(os.environ, **{k: v for k, v in environment.items() if k != 'lean'})
        env['LEAN_PATH'] = str(overlay) + os.pathsep + environment.get('LEAN_PATH', '')
        for name in ('OriginCoverage', 'UnsupportedAxiom'):
            source = overlay / 'LeanCiControls' / (name + '.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text((assets_directory() / 'Controls' / source.name).read_text())
            _compile(lean, source, source.with_suffix('.olean'), overlay, env)
        control_env = dict(environment, LEAN_PATH=env['LEAN_PATH'])
        captured = io.StringIO()
        with contextlib.redirect_stdout(captured):
            status = run_origins('axioms', overlay,
                                 [['LeanCiControls', 'OriginCoverage'],
                                  ['LeanCiControls', 'UnsupportedAxiom']], environment=control_env)
        rows = [json.loads(line) for line in captured.getvalue().splitlines() if line.startswith('{')]
        positive = next((r for r in rows if r['module'] == 'LeanCiControls.OriginCoverage'), {})
        negative = next((r for r in rows if r['module'] == 'LeanCiControls.UnsupportedAxiom'), {})
        inventory = positive.get('result', {}).get('inventory', [])
        good = (status == 1 and positive.get('success') is True and negative.get('success') is False
                and 'LeanCiForeign.Generated.rec' in inventory
                and any(n.startswith('_private.') and n.endswith('.hidden') for n in inventory)
                and any('forbidden' in d for d in negative.get('result', {}).get('diagnostics', [])))
        emit({'kind': 'controls', 'module': 'common-private-generated-axioms', 'success': good,
              'positive_inventory_count': len(inventory),
              'negative_diagnostics': negative.get('result', {}).get('diagnostics', [])})
        compile_status = run_expected_failure(root, [assets_directory() / 'Controls/ExpectedFailure.lean'],
                                               environment=environment)
        return int(not good or compile_status != 0)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kind', choices=KINDS)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--modules', nargs='*', default=[])
    parser.add_argument('--selection-json', type=Path)
    parser.add_argument('--config', type=Path)
    parser.add_argument('--results-jsonl', type=Path)
    parser.add_argument('--changed-path', action='append', default=[])
    args = parser.parse_args(argv)
    try:
        root = args.root.resolve()
        if args.changed_path and args.kind != 'source':
            raise ValueError('--changed-path is supported only for source checks')
        _validate_native_policy(args.kind, args.config)
        selected = json.loads(args.selection_json.read_text()) if args.selection_json else None
        if args.kind in ('source', 'builtin', 'controls') or (args.kind == 'expected-failure' and args.config is not None):
            from . import guards
            return guards.run(args.kind, root, args.modules, config_path=args.config,
                              selection_json=args.selection_json,
                              **({'changed_paths': args.changed_path} if args.kind == 'source' else {}))
        if args.kind == 'expected-failure':
            paths = selected if selected is not None else [str(module_path(m)) for m in args.modules]
            if not isinstance(paths, list) or not all(isinstance(p, str) for p in paths):
                raise ValueError('Expected-failure selection is an array of exact source paths')
            return run_expected_failure(root, [Path(p) for p in paths])
        metadata = None
        if isinstance(selected, dict):
            if args.kind not in ('declarations', 'axioms', 'inventory') or selected.get('schema') != 1 or selected.get('kind') != args.kind or not isinstance(selected.get('invocation'), str) or not selected['invocation']:
                raise ValueError('Invalid native batch selection envelope')
            items = selected.get('items')
            if not isinstance(items, list) or not items or not all(isinstance(item, dict) and
                    all(isinstance(item.get(k), str) and item[k] for k in ('id', 'module', 'input_key')) and
                    isinstance(item.get('components'), list) and item['components'] == module_components(item['module']) for item in items):
                raise ValueError('Invalid native batch items')
            indexed = {tuple(item['components']): item for item in items}
            if len(indexed) != len(items) or len({item['id'] for item in items}) != len(items):
                raise ValueError('Native batch origins and item ids must be unique')
            metadata = {'invocation': selected['invocation'], 'kind': args.kind, 'items': indexed}
            selected = [item['components'] for item in items]
        components = selected if selected is not None else [module_components(m) for m in args.modules]
        if not isinstance(components, list) or not all(isinstance(cs, list) and cs and
                all(isinstance(c, str) and c and c not in ('.', '..') and
                    not any(x in c for x in ('/', '\\')) and
                    not any(ord(x) < 32 or 127 <= ord(x) <= 159 for x in c) for c in cs)
                for cs in components):
            raise ValueError('Selection must be nonempty arrays of safe module-name components')
        if args.kind == 'style':
            modules = args.modules or ['.'.join(('«' + c + '»') if '.' in c or ' ' in c else c for c in cs)
                                       for cs in components]
            return run_style(root, modules)
        return run_origins(args.kind, root, components, metadata=metadata, results_jsonl=args.results_jsonl, config_path=args.config)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print('Native check failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
