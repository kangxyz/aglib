#!/usr/bin/env bash
# CI source-checkout entry; the installed toolkit owns the adapter.
set -euo pipefail
repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
exec bash "$repo/scripts/lean_tools/_lint/run.sh" "$@"
