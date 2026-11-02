#!/usr/bin/env bash
set -euo pipefail
git diff --exit-code 88bab48f8801b48464fe6cce9881c21713001009 HEAD -- '*.lean' lean-toolchain lake-manifest.json lakefile.toml
export LAKE_NO_CACHE=true LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$RUNNER_TEMP/lake-native-cache" LEAN_NUM_THREADS=1
export PATH="$HOME/.elan/bin:$PATH"
# Every native readiness invocation rejects compilation. Availability only:
# these are not new runs of Test/lint/axiom predicates.
lake build --no-build --rehash Aglib AglibTest mathlib/cache batteries/runLinter mathlib/lint-style mathlib/mk_all
auditor="$LAKE_CACHE_DIR/axiom-audit"
test "$(git -C "$auditor" rev-parse HEAD)" = 46024e005996495c65ef609368e11ab39c4222e3
(cd "$auditor" && lake build --no-build --rehash)
test -x "$auditor/.lake/build/bin/axiom-audit"
