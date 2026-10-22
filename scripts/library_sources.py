"""Repository inventory/routing adapter over the shared Lean lexical helpers."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from lean_ci.source import (IDENT, MODULE, IMPORT_START, KEYWORDS,
                            strip_comments_and_strings, lean_imports, import_header,
                            uses_module_system, is_import_surface, module_path, module_name)


def source_modules(root: Path) -> set[Path]:
    return {Path('Aglib.lean')} | {
        path.relative_to(root) for path in (root / 'Aglib').rglob('*.lean')}


def test_modules(root: Path) -> set[Path]:
    """Discover in-package tests without requiring a generated test umbrella."""
    modules = {path.relative_to(root) for path in (root / 'AglibTest').rglob('*.lean')}
    if (root / 'AglibTest.lean').is_file():
        modules.add(Path('AglibTest.lean'))
    return modules


def downstream_sources(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in (root / 'examples/downstream').rglob('*.lean')
            if '.lake' not in path.relative_to(root).parts}
