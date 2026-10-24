# Authors: kangxyz
"""Comment-aware Lean source inventory (Python 3.11+).

Inventory originally adapted alongside the lexical parser from
kangxyz/aglib scripts/library_sources.py,
revision c9863095f90b8bd312af807dbf0e378df82403b5, Apache-2.0.
Copyright (c) 2026 Algebraic geometry contributors; Authors: kangxyz.
The project inventory below is specific to Motivic; lexical grammar is shared
through lean_tools.source.
"""
from pathlib import Path
import re

from ..source import (lean_imports, strip_comments_and_strings, uses_module_system,
                      is_import_surface, module_name, module_path)


ROOTS = ('Motivic', 'MotivicTest')


def source_modules(root: Path) -> dict[str, Path]:
    """Include occupied roots and leaves; never invent a missing facade."""
    result = {}
    for name in ROOTS:
        facade = root / (name + '.lean')
        if facade.is_file():
            result[name] = facade
        for path in (root / name).rglob('*.lean'):
            result[module_name(path.relative_to(root))] = path
    return result


def client_sources(root: Path) -> dict[str, Path]:
    """Inventory the independent client in its own module-resolution namespace."""
    client = root / 'examples/downstream'
    return {module_name(path.relative_to(client)): path
            for path in client.rglob('*.lean')
            if '.lake' not in path.relative_to(client).parts}
