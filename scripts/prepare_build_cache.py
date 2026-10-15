#!/usr/bin/env python3
"""Prepare only package-owned cached builds before the complete --rehash check.

Unknown or compiler-incompatible stamps discard project outputs, never dependencies.
Compatible caches retain current modules and let Lake --rehash check configuration.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import sys

from cache_key import config_hash
from library_sources import (audit_sources, downstream_sources, source_modules,
                             test_modules)

SCHEMA = 'aglib-project-build-v1'
STAMP = '.aglib-cache.json'
PACKAGES = (Path('.'), Path('examples/downstream'))


def _safe_build(root: Path, package: Path) -> Path:
    """Reject redirected build roots and descendants before any cache mutation."""
    path = root
    for component in (package / '.lake/build').parts:
        path = path / component
        if path.is_symlink():
            raise ValueError(f'refusing symlink in project build path: {path}')
        if path.exists() and not path.is_dir():
            raise ValueError(f'project build path is not a directory: {path}')
    # Path.rglob does not follow directory symlinks. Reject them as well as file
    # symlinks; no restored build may redirect removal or stamp writes elsewhere.
    if path.exists():
        for entry in path.rglob('*'):
            if entry.is_symlink():
                raise ValueError(f'refusing symlink in project build: {entry}')
    return path


def _modules(root: Path, package: Path) -> set[str]:
    if package == Path('.'):
        sources = source_modules(root) | test_modules(root) | {
            path for path in audit_sources(root)
            if path == Path('AglibTest/AuditSupport.lean')}
    else:
        sources = {path.relative_to(package) for path in downstream_sources(root)}
    return {path.with_suffix('').as_posix() for path in sources}


def _prune(build: Path, modules: set[str]) -> int:
    removed = 0
    # Lake stores module facets (including compound .olean.private/hash and .c.o
    # suffixes) under these package-owned directories. Dependencies live outside.
    for relative in ('lib/lean', 'ir'):
        directory = build / relative
        if not directory.exists():
            continue
        if not directory.is_dir():
            raise ValueError(f'module artifact path is not a directory: {directory}')
        for path in directory.rglob('*'):
            if path.is_file():
                name = path.relative_to(directory)
                module = (name.parent / name.name.split('.', 1)[0]).as_posix()
                if module not in modules:
                    path.unlink()
                    removed += 1
        for path in sorted(directory.rglob('*'), key=lambda path: len(path.parts), reverse=True):
            if path.is_dir() and not any(path.iterdir()):
                path.rmdir()
    return removed


def prepare(root: Path, compiler_id: str, downstream_compiler_id: str) -> list[str]:
    if not compiler_id.strip() or not downstream_compiler_id.strip():
        raise ValueError('both actual compiler identities are required')
    root = root.resolve(strict=True)
    # Read required configuration and validate both output roots before writing.
    # Client configuration includes root pins/options because it imports Aglib.
    configurations = (config_hash(root, ('',)), config_hash(root))
    builds = [_safe_build(root, package) for package in PACKAGES]
    identities = (compiler_id.strip(), downstream_compiler_id.strip())
    result = []
    for package, build, configuration, compiler in zip(
            PACKAGES, builds, configurations, identities):
        modules = _modules(root, package)
        expected = {'schema': SCHEMA, 'configuration': configuration, 'compiler': compiler,
                    'toolchain': (root / package / 'lean-toolchain').read_text()}
        try:
            previous = json.loads((build / STAMP).read_text())
        except (OSError, ValueError):
            previous = None
        compatible = (isinstance(previous, dict) and previous.keys() == expected.keys()
                      and isinstance(previous.get('configuration'), str)
                      and re.fullmatch(r'[0-9a-f]{64}', previous['configuration']) is not None
                      and all(previous.get(field) == expected[field]
                              for field in ('schema', 'compiler', 'toolchain')))
        if not compatible:
            if build.exists():
                shutil.rmtree(build)
            removed = 'reset (unknown or changed compiler/toolchain)'
        else:
            removed = f'preserved; pruned {_prune(build, modules)} obsolete module facets'
        build.mkdir(parents=True, exist_ok=True)
        (build / STAMP).write_text(json.dumps(expected, sort_keys=True) + '\n')
        result.append(f'{package / ".lake/build"}: {removed}')
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--compiler-id', required=True, help='actual root lean --version output')
    parser.add_argument('--downstream-compiler-id', required=True,
                        help='actual downstream lean --version output')
    args = parser.parse_args()
    try:
        print('\n'.join(prepare(args.root, args.compiler_id, args.downstream_compiler_id)))
    except (OSError, ValueError) as error:
        print(f'project cache preparation error: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
