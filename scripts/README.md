# Local developer tools

Run from the package root with Python 3.11 or newer. The native check entry is:

```sh
bash scripts/check.sh
bash scripts/check.sh --base ACCEPTED_COMMIT --progress /absolute/check-progress
bash scripts/check.sh --source-only
bash scripts/check.sh --list
```

`check.sh` forwards to `check_affected.py`, a thin wrapper around `lean_ci.cli`.
It supplies the `Aglib` production root, existing source guards and Aglib's resource
configuration. There is no separate adapter, hosted-baseline, phase or frozen
request protocol. The [development guide](../docs/DEVELOPMENT.md) describes the
native build/Test/generated-entry/text/lint/axiom commands and trust boundaries.
Use direct focused `lake build +Module.Name` during proof iteration.

## Shared native helpers

`lean_ci/` contains the existing native command, resource, build, source and
successful-check reuse helpers. Its implementation is moved here from the
retired `ci/` directory; no second executor or audit implementation is added.
Python 3.11 or newer is required. The package and console-command names remain
compatible with existing callers.

```sh
python3 -m pip install /absolute/path/to/aglib/scripts
PYTHONPATH=/absolute/path/to/aglib/scripts python3 -m lean_ci check \
  --root /absolute/package --production Aglib
```

The check CLI accepts optional `--check-target`, `--base`/`--head`, `--full`,
`--source-only`, `--progress`, `--state`/`--receipt-dir`, `--outputs` and `--list`.
Focused `lean-ci build` uses one incremental native Lake build. Lake controls
compilation reuse; compatible lint, entry, text and axiom successes retain their
actual command/checker/input boundary. The existing managed resource profile
passes through unchanged. Generic remote phases can call the same prepared
native helper without a frozen request or CI-baseline protocol.

| Retained tool | Purpose |
| --- | --- |
| `check_library_layout.py` | Source import resolution, production dependency boundary, modern exports, precise imports and cycles; `--generate MODULE` writes one selected topic entry. |
| `check_placeholders.py` | Reject placeholders and custom-axiom tokens in production, in-package tests and standalone client source, masking comments and strings. This is not a transitive axiom audit. |
| `check_source_policy.py` | Retain finite local heartbeat, option, source-safety and author-credit checks. |
| `library_sources.py` | Library-specific inventory/routing over the shared Lean grammar. |
| `build_serial.py` | Compatibility CLI for a selected guarded native module build, using shared `build/resources`. |
| `resource_guard.py` | Compatibility CLI delegating one explicit command to shared resource limits and owned-process monitoring. |
| `migration_helpers.py` | Read-only inspection of historical extraction sources with explicit source revision/hash. Retired writer functions continue to fail before writes. |

Mathlib `mk_all` owns the production root. For a new topic with existing source,
or an existing generator-owned topic entry, run
`python3 scripts/check_library_layout.py --generate Aglib.Topic`; then use
`lake exe mathlib/mk_all --lib Aglib` when root enrollment changes. Generated
topic entries always use `set_option linter.style.longFile 0`, so future growth
needs no recalculated line allowance. Manually maintained entries retain their
ownership. Native Test uses the package test glob without a generated test
umbrella. The upstream production
axiom auditor replaces duplicate custom origin audits and rejection controls.
Its recorded scope is not relabelled as the former checked-environment predicate.
The removed orchestration/cache scripts are not a second local or remote check
path. Generic remote commands may invoke the same native entry with its managed
resource profile and matching prepared dependencies.

Source-policy and wrapper regression suites:

```sh
PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests -p test_source_guards.py
PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests -p test_check_script.py
PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests -p test_build_serial.py
PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests -p test_migration_helpers.py
```

`test_lean_ci_workflow.py` independently checks the existing public workflow;
it is not modified by the local-entry migration. Shared resource/runtime/progress
fixtures live under `scripts/tests/`. No test here establishes
mathematical source correspondence or discharges theorem premises.

Run the combined bounded Python suites with `PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests`.
