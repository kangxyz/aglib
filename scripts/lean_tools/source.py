"""Lean names, import-header grammar and shared source-graph discovery.

Inventory adapted from kangxyz/aglib scripts/library_sources.py at
c9863095f90b8bd312af807dbf0e378df82403b5, Apache-2.0.
Copyright (c) 2026 Algebraic geometry contributors; Authors: kangxyz.
"""
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
    """Read the header's one-module import directives from pinned Lean 4 syntax."""
    return import_header(strip_comments_and_strings(source))[0]


def import_header(clean: str) -> tuple[list[str], int]:
    """Return imports and the start of the body, without guessing command keywords.

    Lean/Parser/Module/Syntax.lean gives each import exactly one module name.
    Whitespace can separate a directive from its name or successive directives.
    """
    def whitespace(position):
        while position < len(clean) and clean[position].isspace():
            position += 1
        return position

    position = whitespace(0)
    for keyword in ('module', 'prelude'):
        match = re.match(keyword + r'\b', clean[position:])
        if match:
            position = whitespace(position + match.end())
    imports = []
    directive = re.compile(r'(?:public\s+)?(?:meta\s+)?import\b')
    while start := directive.match(clean, position):
        after = whitespace(start.end())
        # `all` modifies the import; it is not a module named `all`.
        modifier = re.match(r'all\b', clean[after:])
        if modifier:
            after = whitespace(after + modifier.end())
        match = MODULE.match(clean, after)
        if not match or match.group() in KEYWORDS:
            break
        # Normalize quoted ordinary identifiers to prevent namespace bypasses.
        token = re.sub(r'«([^»]+)»', lambda m: m[1] if
                       re.fullmatch(r'[^\W\d]\w*', m[1]) else m[0], match.group())
        imports.append(token)
        position = whitespace(match.end())
    return imports, position


def uses_module_system(source: str) -> bool:
    """Recognize a real module header after comments, rather than quoted prose."""
    return re.match(r'\s*module\b', strip_comments_and_strings(source)) is not None


def is_import_surface(source: str) -> bool:
    """Recognize import-only APIs without classifying a foundational module as a facade.

    Empty public sections added by a module migration do not add declarations.
    Other commands conservatively keep the source classified as implementation.
    """
    clean = strip_comments_and_strings(source)
    _, position = import_header(clean)
    remaining = clean[position:].lstrip()
    # Generated import surfaces can exceed the proof-file size bound. This
    # metadata does not turn a facade into a mathematical implementation.
    remaining = re.sub(r'^set_option\s+linter\.style\.longFile\s+\d+\s*', '', remaining)
    return re.fullmatch(r'(?:@\[\s*expose\s*\]\s*)?(?:public\s+)?(?:meta\s+)?section\s*',
                        remaining) is not None or not remaining


def module_path(module: str) -> Path:
    parts = [part[1:-1] if part.startswith('«') else part
             for part in re.findall(IDENT, module)]
    return Path(*parts[:-1], parts[-1] + '.lean')


def module_name(path: Path | str) -> str:
    return Path(path).with_suffix('').as_posix().replace('/', '.')




def source_modules(root, roots=None):
    """Discover occupied project roots and leaves, including in-package tests."""
    from .library import profile
    root = Path(root)
    if roots is None:
        production = profile(root)['production']
        roots = (production, production + 'Test')
    result = {}
    for name in roots:
        facade = root / (name + '.lean')
        if facade.is_file():
            result[name] = facade
        result.update({module_name(path.relative_to(root)): path
                       for path in (root / name).rglob('*.lean')})
    return result

def client_sources(root):
    root = Path(root) / 'examples/downstream'
    return {module_name(path.relative_to(root)): path for path in root.rglob('*.lean')
            if '.lake' not in path.relative_to(root).parts}

def import_cycles(graph):
    """Iterative DFS supports dependency chains beyond Python's recursion limit."""
    state, cycles = {}, []
    for entry in sorted(graph):
        if state.get(entry):
            continue
        state[entry] = 1
        stack = [(entry, iter(sorted(graph[entry])))]
        while stack:
            node, children = stack[-1]
            child = next(children, None)
            if child is None:
                state[node] = 2
                stack.pop()
            elif state.get(child) == 1:
                route = [item[0] for item in stack]
                cycles.append(' -> '.join(route[route.index(child):] + [child]))
            elif child in graph and not state.get(child):
                state[child] = 1
                stack.append((child, iter(sorted(graph[child]))))
    return cycles
