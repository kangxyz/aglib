#!/usr/bin/env bash
# All scopes use the same incremental recipe and compatible check progress.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check_affected.py "$@"
