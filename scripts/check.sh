#!/usr/bin/env bash
# Separately requested comprehensive diagnostics and declared CI only; normal local checks must be incremental. Source-only is read-only.
set -euo pipefail
cd "$(dirname "$0")/.."
source_only=0
ci_mode=0
lake_args=()
for argument in "$@"; do
  case "$argument" in
    --source-only) source_only=1 ;;
    --rehash) lake_args+=(--rehash) ;;
    --ci) ci_mode=1 ;;
    *) echo "Usage: $0 [--source-only] [--rehash] [--ci]" >&2; exit 2 ;;
  esac
done
python3 scripts/generate_imports.py --check
python3 scripts/check_library_layout.py
python3 scripts/check_placeholders.py
python3 scripts/check_source_policy.py
python3 -m unittest discover -s scripts -p 'test_*.py'
if (( source_only )); then
  exit 0
fi
verification_dir="${AGLIB_VERIFY_DIR:-$PWD/.lake/verification/$(date +%Y%m%d-%H%M%S)}"
project_root="$PWD"
export LEAN_NUM_THREADS=1
if (( ci_mode )); then
  echo "CI scope: build/lint/axiom/control/inventory/client checks; publication replay coverage may reuse compatible local evidence."
fi
safe() {
  local phase="$1"
  shift
  python3 "$project_root/scripts/resource_guard.py" --capped-toolchain \
    --receipt "$verification_dir/$phase.json" -- "$@"
}
python3 scripts/build_serial.py --receipt-dir "$verification_dir/build" \
  ${lake_args[@]+"${lake_args[@]}"} Aglib AglibTest AglibTest.AuditSupport
safe test lake ${lake_args[@]+"${lake_args[@]}"} test
if (( ci_mode )); then
  # CI owns writable dependency caches, so use Mathlib's native Lake entry points.
  # A single `lake lint` keeps its builtin phase's environment mapped while the
  # Batteries driver runs, and the two together exceed the CI memory budget, so
  # the builtin phase and the driver run as separate guarded processes.
  safe builtin-lint lake ${lake_args[@]+"${lake_args[@]}"} lint --builtin-only
  safe declaration-lint lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Aglib
  safe style lake ${lake_args[@]+"${lake_args[@]}"} exe mathlib/lint-style Aglib AglibTest
else
  # Execute the same pinned Lean linters without changing shared dependency caches.
  safe declaration-lint lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Aglib
  safe style python3 scripts/run_style_linter.py
fi
# Cached oleans do not re-execute the trust audit, so replay the source explicitly.
safe axioms lake env lean -j1 AglibTest/Axioms.lean
safe negative-controls python3 scripts/check_negative_controls.py
# Check exact current inventory, including private/generated declarations.
python3 scripts/check_compiled_inventory.py
if (( ! ci_mode )); then
  python3 scripts/check_kernel.py --receipt-dir "$verification_dir/kernel"
fi
python3 scripts/prepare_downstream.py
(
  cd examples/downstream
  python3 "$project_root/scripts/build_serial.py" --receipt-dir "$verification_dir/client-build" \
    ${lake_args[@]+"${lake_args[@]}"} Consumer
  safe client-audit lake env lean -j1 Audit.lean
  if (( ! ci_mode )); then
    python3 "$project_root/scripts/check_kernel.py" --root "$PWD" --client \
      --receipt-dir "$verification_dir/client-kernel"
  fi
)
