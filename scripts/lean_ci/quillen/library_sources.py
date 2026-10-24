"""Quillen source enrollment, using the toolkit's pinned Lean header grammar."""
from pathlib import Path
from ..source import (lean_imports, module_name, module_path, is_import_surface,
                      strip_comments_and_strings, uses_module_system)

def project_imports(source: str) -> list[str]:
    return [module for module in lean_imports(source)
            if module == 'Quillen' or module.startswith('Quillen.')]


def source_modules(root: Path) -> set[Path]:
    return {Path('Quillen.lean')} | {
        path.relative_to(root) for path in (root / 'Quillen').rglob('*.lean')}


def test_modules(root: Path) -> set[Path]:
    """Test sources are discovered without a generated Test umbrella."""
    return {
        path.relative_to(root) for path in (root / 'QuillenTest').rglob('*.lean')}


def downstream_sources(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in (root / 'examples/downstream').rglob('*.lean')
            if '.lake' not in path.relative_to(root).parts}
