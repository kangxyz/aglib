#!/usr/bin/env python3
"""Reject unlimited or global heartbeat overrides and weakened Lean source policy."""
import argparse
from pathlib import Path
import re
import sys
from library_sources import IDENT, MODULE, source_modules, strip_comments_and_strings

ROOT = Path(__file__).resolve().parents[1]


def check_source_policy(root: Path) -> list[str]:
    errors = []
    for relative in sorted(source_modules(root)):
        source = (root / relative).read_text()
        clean = strip_comments_and_strings(source)
        # Consume whole identifiers first, including quoted names containing spaces,
        # so apparent commands inside quoted identifiers are never inspected.
        tokens = list(re.finditer(MODULE.pattern + r'|[0-9]\w*|\S', clean))
        for index, match in enumerate(tokens[:-2]):
            if match.group() != 'set_option':
                continue
            option = tokens[index + 1].group()
            value_token = tokens[index + 2]
            value = value_token.group()
            line = source.count('\n', 0, match.start()) + 1
            if option == 'autoImplicit' and value == 'true':
                errors.append(f'{relative}:{line}: autoImplicit must remain false')
            if option == 'warningAsError' and value == 'false':
                errors.append(f'{relative}:{line}: warningAsError must remain true')
            if option == 'linter.mathlibStandardSet' and value == 'false':
                errors.append(f'{relative}:{line}: standard mathlib lint set must remain enabled')
            components = [part.strip('«»') for part in re.findall(IDENT, option)]
            if 'maxHeartbeats' in components:
                # Aglib additionally forbids unlimited budgets, including zero in
                # decimal and prefixed numeral spellings. Lean checks syntax.
                numeral = value.replace('_', '')
                if re.fullmatch(r'(?:0+|0[xXbBoO]0+)', numeral):
                    errors.append(f'{relative}:{line}: heartbeat budgets must be positive and finite '
                                  '(zero means unlimited)')
                scope = tokens[index + 3] if index + 3 < len(tokens) else None
                if scope is None or scope.group() != 'in':
                    errors.append(f'{relative}:{line}: heartbeat overrides must be declaration-local')
                else:
                    following = source[scope.end():].lstrip()
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
    print('Source policy checked: fixed source safety and declaration-local, documented, positive finite heartbeat budgets.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
