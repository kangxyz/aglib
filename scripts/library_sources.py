"""Repository inventory/routing adapter over the shared Lean lexical helpers."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'ci'))
from lean_ci.source import (IDENT, MODULE, IMPORT_START, KEYWORDS,
                            strip_comments_and_strings, lean_imports, import_header,
                            uses_module_system, is_import_surface, module_path, module_name)


def project_imports(source: str) -> list[str]:
    return [module for module in lean_imports(source)
            if module == 'Aglib' or module.startswith('Aglib.')]


def source_modules(root: Path) -> set[Path]:
    return {Path('Aglib.lean')} | {
        path.relative_to(root) for path in (root / 'Aglib').rglob('*.lean')}


def is_audit_source(path: Path) -> bool:
    return path in {Path('Audits/Aglib.lean'),
                    Path('AglibTest/AuditSupport.lean')} or \
        'NegativeControls' in path.parts


def audit_sources(root: Path) -> set[Path]:
    return {path.relative_to(root) for directory in ('AglibTest', 'Audits')
            for path in (root / directory).rglob('*.lean')
            if is_audit_source(path.relative_to(root))}


def test_modules(root: Path) -> set[Path]:
    """Positive trust sources are discovered without a generated Test umbrella."""
    return {
        path.relative_to(root) for path in (root / 'AglibTest').rglob('*.lean')
        if not is_audit_source(path.relative_to(root))}


def downstream_sources(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in (root / 'examples/downstream').rglob('*.lean')
            if '.lake' not in path.relative_to(root).parts}


def tool_sources(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in (root / 'Tools').rglob('*.lean')}


def style_sources(root: Path) -> list[tuple[str, Path]]:
    """Enumerate source paths and module identities in their actual packages."""
    sources = source_modules(root) | test_modules(root) | audit_sources(root)
    result = [(module_name(path), path) for path in sources]
    client = Path('examples/downstream')
    result.extend((module_name(path.relative_to(client)), path)
                  for path in downstream_sources(root))
    return sorted(result, key=lambda item: item[1].as_posix())


def import_closure(root: Path, entrypoints: list[str | Path]) -> set[Path]:
    seen: set[Path] = set()
    pending = [Path(path) for path in entrypoints]
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        if not (root / path).is_file():
            raise ValueError(f'Missing project import source: {path}')
        seen.add(path)
        pending.extend(module_path(module)
                       for module in project_imports((root / path).read_text()))
    return seen


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--style-sources', action='store_true', required=True)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    for module, path in style_sources(args.root):
        print(module + '\t' + path.as_posix())
