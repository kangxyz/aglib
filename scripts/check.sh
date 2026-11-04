#!/usr/bin/env bash
# Run the package's native CI checks locally.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/lean_tools/__main__.py check --root "$PWD" "$@"
