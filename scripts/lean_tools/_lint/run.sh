#!/usr/bin/env bash
# Shared packaged adapter. Unsupported inputs retain the native predicate.
set -euo pipefail
helper_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
prepare_only=false
if [[ "${1:-}" == --prepare-only ]]; then
  prepare_only=true
  shift
  (( $# == 0 )) || { echo '--prepare-only takes no roots' >&2; exit 2; }
fi
if ! provider="$(python3 "$helper_dir/preflight.py" --batteries-dir)" ||
   [[ "$(lake env lean --version)" != "Lean (version 4.34.1,"* ]]; then
  if "$prepare_only"; then exit 0; fi
  exec lake --no-build lint "$@" -- --trace
fi
workers="$(python3 - <<'PY'
import os
requested = os.environ.get("CI_LINT_WORKERS", "2")
if not requested.isdecimal() or int(requested) < 1:
    raise SystemExit("CI_LINT_WORKERS must be a positive integer")
available = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)
cap = os.environ.get("LEAN_TOOLS_LINT_MAX_THREADS")
if cap is not None:
    if not cap.isdecimal() or int(cap) < 1:
        raise SystemExit("LEAN_TOOLS_LINT_MAX_THREADS must be a positive integer")
    available = min(available, int(cap))
print(min(int(requested), max(1, available)))
PY
)"
export CI_LINT_WORKERS="$workers"
export LEAN_NUM_THREADS="$workers"
# Build only the CI executable, against native provider objects already prepared by CI.
# Lake may reuse compilation artifacts; full lint results are never reused.
lake --no-build build batteries/runLinter
build="$PWD/.lake/lint-runner"
python3 - "$helper_dir" "$build" "$provider" <<'PY'
import json
from pathlib import Path
import sys
helper, build, provider = map(Path, sys.argv[1:])
build.mkdir(parents=True, exist_ok=True)
config = ('name = "AglibCILintRunner"\nenableArtifactCache = false\n'
          '[[require]]\nname = "batteries"\npath = ' + json.dumps(str(provider)) + '\n'
          '[[lean_exe]]\nname = "batchedLint"\nroot = "BatchedLint"\n'
          'supportInterpreter = true\n')
for name, content in (("lakefile.toml", config),
                      ("lean-toolchain", "leanprover/lean4:v4.34.1\n"),
                      ("BatchedLint.lean", (helper / "BatchedLint.lean").read_text())):
    target = build / name
    if not target.exists() or target.read_text() != content:
        target.write_text(content)
PY
# Select our generated config and re-resolve only this private tool's known path
# dependency. Restored manifests/configs must not redirect the compiled target.
lake --dir "$build" --file lakefile.toml --update --keep-toolchain build batchedLint
if "$prepare_only"; then exit 0; fi
driver_args="$(python3 "$helper_dir/preflight.py" --driver-args)"
builtin_status=0
builtin_start=$SECONDS
lake --no-build --builtin-only lint "$@" || builtin_status=$?
printf 'full lint: builtin exit=%s elapsed=%ss\n' "$builtin_status" "$((SECONDS - builtin_start))"
driver_status=0
lake env "$build/.lake/build/bin/batchedLint" "$driver_args" || driver_status=$?
if (( driver_status != 0 )); then
  exit "$driver_status"
fi
exit "$builtin_status"
