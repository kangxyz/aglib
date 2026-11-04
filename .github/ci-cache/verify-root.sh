#!/usr/bin/env bash
# Verify a local publication stage without using expanded root artifacts.
set -euo pipefail
archive=$1
shift
test "$#" -gt 0
python3 -B - <<'PY'
from pathlib import Path
import sys

sys.path.insert(0, '.github/ci-cache')
from checkpoint import configuration, default_build_layout

root = Path.cwd()
if not (root / 'lakefile.toml').is_file() or (root / 'lakefile.lean').exists():
    raise SystemExit('Same-host CI requires a standard TOML root build layout')
default_build_layout(configuration(root))
PY
if ! test -d .lake/build || test -L .lake || test -L .lake/build; then
  echo '::error::Expected a runner-owned root build directory.'
  exit 1
fi
scratch=$(mktemp -d "$PWD/.lake/ci-stage-check.XXXXXX")
restore_build() {
  if test -d "$scratch/original"; then
    rm -rf -- .lake/build || return 1
    mv -- "$scratch/original" .lake/build || return 1
  fi
  rm -rf -- "$scratch"
}
trap restore_build EXIT
# Reuse the pinned dependency working tree, but let only the exact
# publication archive supply root outputs to this no-build check.
mkdir "$scratch/stage"
tar -xf "$archive" -C "$scratch/stage"
mv -- .lake/build "$scratch/original"
(
  export LAKE_CACHE_DIR="$scratch/native" LAKE_RESTORE_ARTIFACTS=true
  lake cache unstage "$scratch/stage" --force-overwrite
  lake build --no-build --rehash "$@"
)
restore_build
trap - EXIT
