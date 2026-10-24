#!/usr/bin/env python3
"""Reject proof placeholders and custom axioms in library, tests and client.

The native upstream axiom auditor checks transitive dependencies after compilation.
"""
import argparse
from pathlib import Path
import re
import sys

from .sources import (downstream_sources, source_modules,
                             strip_comments_and_strings, test_modules)

ROOT = Path.cwd()


def check_placeholders(root: Path) -> list[str]:
    errors = []
    sources = source_modules(root) | test_modules(root) | downstream_sources(root)
    for relative in sorted(sources):
        source = (root / relative).read_text()
        clean = strip_comments_and_strings(source)
        for match in re.finditer(r'\b(sorry|admit|axiom)\b', clean):
            line = source.count('\n', 0, match.start()) + 1
            errors.append(f'{relative}:{line}: forbidden token {match.group()}')
    return errors


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args(argv)
    try:
        errors = check_placeholders(args.root)
    except OSError as error:
        print(f'Source-token check failed: {error}', file=sys.stderr)
        return 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print('Source-token check passed: no proof placeholders or custom assumptions.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
