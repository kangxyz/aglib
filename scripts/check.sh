#!/usr/bin/env bash
# The package owns the native commands and Aglib source policy.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/lean_ci/__main__.py check --root "$PWD" "$@"
