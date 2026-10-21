#!/usr/bin/env python3
"""Compatibility entry point for the installable common native-cache transport."""
from pathlib import Path
import sys

# The action checkout contains its pinned common package; installed users call
# lean_ci.transport.cache directly and have no repository-relative dependency.
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'ci' / 'src'))
from lean_ci.transport import cache as cache_transport

if __name__ == '__main__':
    raise SystemExit(cache_transport.main())
else:
    # Preserve the public action module identity for existing import consumers.
    sys.modules[__name__] = cache_transport
