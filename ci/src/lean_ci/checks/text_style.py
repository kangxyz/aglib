"""Read-only compatibility for the three extant pinned Mathlib Python style rules.

The vendor script is never edited. Only the two retained in-memory repairs are
applied; nonterminal_simp_check was retired upstream and is not reinstated.
"""
from hashlib import sha256
from pathlib import Path
import sys

EXPECTED_SHA256 = '1996b93b5831ea31422db18aeb26d2884762f04530d4aaa220deb56703f658f0'
REPAIRS = (
    ('enum_lines = enumerate(lines, 1)', 'enum_lines = list(enumerate(lines, 1))'),
    ('left_arrow_check,\n                            nonterminal_simp_check]',
     'left_arrow_check]'),
)


def patched_source(raw: bytes) -> str:
    actual = sha256(raw).hexdigest()
    if actual != EXPECTED_SHA256:
        raise ValueError(f'unsupported lint-style.py SHA256: {actual}')
    source = raw.decode('utf-8')
    for before, after in REPAIRS:
        if source.count(before) != 1:
            raise ValueError(f'expected exactly one repair site: {before!r}')
        source = source.replace(before, after, 1)
    return source


def run(script: Path, sources: list[Path]) -> int:
    """Evaluate unchanged vendor rule bodies with exact selected source paths."""
    if not sources or any(str(source) == '--fix' for source in sources):
        raise ValueError('Pinned text style needs exact source files; --fix is unsupported')
    source = patched_source(Path(script).read_bytes())
    previous = sys.argv
    try:
        sys.argv = [str(script), *map(str, sources)]
        exec(compile(source, str(script), 'exec'), {'__name__': '__main__', '__file__': str(script)})
    except SystemExit as result:
        if result.code is None:
            return 0
        if not isinstance(result.code, int):
            raise RuntimeError(f'Pinned text style failed: {result.code}')
        return result.code
    finally:
        sys.argv = previous
    return 0
