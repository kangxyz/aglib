"""The packaged full-lint adapter and its observed source and native inputs."""
import json
from pathlib import Path
import tomllib
import types

from .source import lean_imports

ASSETS = Path(__file__).resolve().with_name('_lint')


def command(roots=(), *, prepare=False):
    return ['bash', str(ASSETS / 'run.sh'), *(['--prepare-only'] if prepare else roots)]


def adapter_sources():
    return [Path(__file__).resolve(), *(ASSETS / name for name in
            ('run.sh', 'preflight.py', 'BatchedLint.lean'))]


def supported_provider(root):
    # Read the same source as the subprocess, without a stale imported bytecode cache.
    path = ASSETS / 'preflight.py'
    module = types.ModuleType('_lean_tools_lint_preflight')
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module.provider_directory(Path(root))


def context(root):
    """Resolve recognized driver roots for observation, without admitting reuse."""
    root = Path(root)
    provider = supported_provider(root)
    if not provider:
        return None
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    args = config['lintDriverArgs']
    return {'provider': provider,
            'driver_roots': [arg for arg in args if not arg.startswith('-')]}


def source_inputs(root):
    """Immutable adapter/config/provider sources; generated files are separate."""
    root = Path(root)
    paths = [*adapter_sources(), root / '.lake/package-overrides.json']
    try:
        config = tomllib.loads((root / 'lakefile.toml').read_text())
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        for entry in manifest.get('packages', []):
            if entry.get('name') != 'batteries':
                continue
            directory = (root / entry['dir'] if entry.get('type') == 'path' else
                         root / config.get('packagesDir', '.lake/packages') / 'batteries')
            if entry.get('subDir'):
                directory /= entry['subDir']
            paths += [directory / name for name in ('lakefile.toml', 'lakefile.lean',
                'lake-manifest.json', 'lean-toolchain', 'scripts/runLinter.lean',
                'Batteries/Tactic/Lint.lean', 'Batteries/Tactic/Lint/Basic.lean',
                'Batteries/Tactic/Lint/Frontend.lean', 'Batteries/Tactic/Lint/Misc.lean',
                'Batteries/Tactic/Lint/Simp.lean', 'Batteries/Tactic/Lint/TypeClass.lean')]
    except (OSError, ValueError, KeyError, TypeError):
        pass  # Native fallback diagnoses unsupported inputs; lint always runs.
    return paths


def generated_inputs(root):
    """The preparation stage creates these before the consuming check is bound."""
    tool = Path(root) / '.lake/lint-runner'
    return [tool / name for name in ('BatchedLint.lean', 'lakefile.toml', 'lean-toolchain',
                                     '.lake/build/bin/batchedLint') if (tool / name).is_file()]


def import_roots(root, production):
    selected = context(root)
    roots = [*production, *lean_imports((ASSETS / 'BatchedLint.lean').read_text())]
    if selected:
        roots += selected['driver_roots']
        source = selected['provider'] / 'scripts/runLinter.lean'
        roots += lean_imports(source.read_text())
    return sorted(set(roots))
