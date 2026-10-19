"""Source-only Lean import inventory; no Lake or checkpoint dependency."""
from pathlib import Path
import re

# Lean identifiers used as module components, including quoted identifiers.
IDENT = r'(?:[^\W\d][\w\u0080-\uffff\'!?]*|«[^»\n]+»)'
MODULE = re.compile(IDENT + r'(?:\.' + IDENT + r')*')
IMPORT_START = re.compile(r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b', re.M)
KEYWORDS = {'import', 'all', 'public', 'private', 'meta', 'prelude', 'module', 'namespace',
            'section', 'end', 'open', 'set_option', 'noncomputable', 'universe',
            'variable', 'def', 'theorem', 'lemma', 'example', 'instance', 'abbrev',
            'axiom', 'constant', 'class', 'structure', 'inductive', 'attribute',
            'export', 'initialize', 'mutual', 'syntax', 'macro', 'elab', 'run_cmd'}


def strip_comments_and_strings(source: str) -> str:
    """Mask nested Lean comments and escaped strings, retaining token boundaries.

    A masked string is a non-whitespace sentinel, so an import cannot continue
    through a string into apparent module names later in the source.
    """
    result = list(source)
    i, depth = 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                result[i:i + 2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                result[i:i + 2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n':
                    result[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            result[i:i + 2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                result[i] = ' '; i += 1
        elif source[i] == '"':
            result[i] = '#'; i += 1
            while i < len(source):
                char = source[i]
                if char != '\n':
                    result[i] = ' '
                i += 1
                if char == '\\' and i < len(source):
                    if source[i] != '\n':
                        result[i] = ' '
                    i += 1
                elif char == '"':
                    break
        elif source[i] == '«':
            # Comment/string delimiters inside a quoted identifier are literal.
            end = source.find('»', i + 1)
            i = len(source) if end < 0 else end + 1
        else:
            i += 1
    return ''.join(result)


def lean_imports(source: str) -> list[str]:
    """Read single/multiple/multiline imports with optional Lean modifiers."""
    clean = strip_comments_and_strings(source)
    imports = []
    for start in IMPORT_START.finditer(clean):
        position = start.end()
        # `all` modifies the import; it is not a module named `all`.
        modifier = re.match(r'\s+all\b', clean[position:])
        if modifier:
            position += modifier.end()
        while position < len(clean):
            while position < len(clean) and clean[position].isspace():
                position += 1
            match = MODULE.match(clean, position)
            if not match or match.group() in KEYWORDS:
                break
            # Normalize quoted ordinary identifiers to prevent namespace bypasses.
            token = re.sub(r'«([^»]+)»', lambda m: m[1] if
                           re.fullmatch(r'[^\W\d]\w*', m[1]) else m[0], match.group())
            imports.append(token)
            position = match.end()
    return imports


def uses_module_system(source: str) -> bool:
    """Recognize a real module header after comments, rather than quoted prose."""
    return re.match(r'\s*module\b', strip_comments_and_strings(source)) is not None


def is_import_surface(source: str) -> bool:
    """Recognize import-only APIs without classifying a foundational module as a facade.

    Empty public sections added by a module migration do not add declarations.
    Other commands conservatively keep the source classified as implementation.
    """
    remaining = strip_comments_and_strings(source).lstrip()
    remaining = re.sub(r'^module\b\s*', '', remaining)
    remaining = re.sub(r'^prelude\b\s*', '', remaining)
    while match := IMPORT_START.match(remaining):
        position = match.end()
        modifier = re.match(r'\s+all\b', remaining[position:])
        if modifier:
            position += modifier.end()
        while position < len(remaining):
            while position < len(remaining) and remaining[position].isspace():
                position += 1
            token = MODULE.match(remaining, position)
            if not token or token.group() in KEYWORDS:
                break
            position = token.end()
        remaining = remaining[position:].lstrip()
    # Generated import surfaces can exceed the proof-file size bound. This
    # metadata does not turn a facade into a mathematical implementation.
    remaining = re.sub(r'^set_option\s+linter\.style\.longFile\s+\d+\s*', '', remaining)
    return re.fullmatch(r'(?:@\[\s*expose\s*\]\s*)?(?:public\s+)?(?:meta\s+)?section\s*',
                        remaining) is not None or not remaining


def project_imports(source: str) -> list[str]:
    return [module for module in lean_imports(source)
            if module == 'Aglib' or module.startswith('Aglib.')]


def module_path(module: str) -> Path:
    parts = [part[1:-1] if part.startswith('«') else part
             for part in re.findall(IDENT, module)]
    return Path(*parts[:-1], parts[-1] + '.lean')


def module_name(path: Path | str) -> str:
    return Path(path).with_suffix('').as_posix().replace('/', '.')


def source_modules(root: Path) -> set[Path]:
    return {Path('Aglib.lean')} | {
        path.relative_to(root) for path in (root / 'Aglib').rglob('*.lean')}


def is_audit_source(path: Path) -> bool:
    return path in {Path('AglibTest/Axioms.lean'),
                    Path('AglibTest/AuditSupport.lean')} or \
        'NegativeControls' in path.parts


def audit_sources(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in (root / 'AglibTest').rglob('*.lean')
            if is_audit_source(path.relative_to(root))}


def test_modules(root: Path) -> set[Path]:
    """Positive trust tests have a separate generated integration root."""
    if not (root / 'AglibTest').exists() and not (root / 'AglibTest.lean').exists():
        return set()
    return {Path('AglibTest.lean')} | {
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
