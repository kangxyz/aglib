#!/usr/bin/env python3
"""Reject global heartbeat overrides and weakening of fixed Lean source policy."""
import argparse
from pathlib import Path
import re
import sys
from library_sources import IDENT, source_modules, strip_comments_and_strings

ROOT = Path(__file__).resolve().parents[1]


def check_source_policy(root: Path) -> list[str]:
    errors = []
    for relative in sorted(source_modules(root)):
        source = (root / relative).read_text()
        clean = strip_comments_and_strings(source)
        for match in re.finditer(r'\bset_option\s+(\S+)\s+(\S+)', clean):
            option, value = match.groups()
            line = source.count('\n', 0, match.start()) + 1
            if option == 'autoImplicit' and value == 'true':
                errors.append(f'{relative}:{line}: autoImplicit must remain false')
            if option == 'warningAsError' and value == 'false':
                errors.append(f'{relative}:{line}: warningAsError must remain true')
            if option == 'linter.mathlibStandardSet' and value == 'false':
                errors.append(f'{relative}:{line}: standard mathlib lint set must remain enabled')
            components = [part.strip('«»') for part in re.findall(IDENT, option)]
            if 'maxHeartbeats' in components:
                # Match pinned Mathlib: any maxHeartbeats name component is
                # declaration-scoped and has a comment after `in`. Lean checks
                # option-value syntax; documented local 0 is not separately banned.
                tail = clean[match.end():]
                scoped = re.match(r'\s+in\b', tail)
                if scoped is None:
                    errors.append(f'{relative}:{line}: heartbeat overrides must be declaration-local')
                else:
                    following = source[match.end() + scoped.end():].lstrip()
                    if not following.startswith(('--', '/-')):
                        errors.append(f'{relative}:{line}: local heartbeat modification needs '
                                      'an explanatory comment after in')
        for match in re.finditer(r'\b(?:constant|unsafe\s+(?:def|opaque))\b', clean):
            errors.append(f'{relative}:{source.count(chr(10), 0, match.start()) + 1}: '
                          'unsupported source assumption or unsafe implementation')
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    try:
        errors = check_source_policy(args.root)
    except OSError as error:
        print(error, file=sys.stderr)
        return 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print('Source policy checked: fixed source safety and Mathlib-scoped, documented heartbeat modifications.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
