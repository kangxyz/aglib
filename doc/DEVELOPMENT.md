# Development and checks

Run commands from the package root. [lean-toolchain](../lean-toolchain) pins Lean 4.34.1; [lakefile.toml](../lakefile.toml) pins Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and declares `Aglib` and `AglibTest`. Keep the pinned [lake-manifest.json](../lake-manifest.json). Production imports use Mathlib and precise lower `Aglib` leaves.

## Setup and focused builds

Fetch matching official Mathlib artifacts through the maintained resource guard:

```sh
python3 scripts/resource_guard.py --bootstrap-cache \
  --receipt .lake/verification/cache-bootstrap.json -- lake exe cache get
```

The bootstrap mode accepts only that exact cache command. It retains the process-group RSS cutoff and capped compiler threads while allowing the cache tool's compiler children. Normal project proof work uses the sequential route.

Build a changed leaf and its affected consumers with [build_serial.py](../scripts/build_serial.py):

```sh
python3 scripts/build_serial.py --receipt-dir .lake/verification/iteration \
  Aglib.CategoryTheory.ExactCategory.Basic
```

The helper accepts `--root ROOT`, `--rehash` and one or more module targets. It first checks whether the requested targets are already cached, then invokes one ordinary Lake build graph for missing work. Lake schedules dependencies with one capped Lean compiler process at a time; `AGLIB_BUILD_THREADS` selects that compiler's internal parallelism. Expected out-of-date diagnostics from the cache probe are saved in `cached-check.log`; configuration, tool and compilation failures still fail the check. [resource_guard.py](../scripts/resource_guard.py) supplies the same owned-group guard for other commands through `--capped-toolchain --receipt FILE -- COMMAND`. [scripts/README.md](../scripts/README.md) owns detailed runtime and helper interfaces.

## Local verification and CI

[check.sh](../scripts/check.sh) is the integration route. Source-only checks verify generated enrollment, occupied structure, import direction, public source policy, placeholders and the Python regression suite:

```sh
bash scripts/check.sh --source-only
```

The full local route includes the extra independent kernel replays for the library and downstream client:

```sh
bash scripts/check.sh --rehash
```

`--rehash` asks Lake to validate current source and build arguments while retaining unaffected outputs. Coordinate integrated checks with the integrator; they write shared build outputs and must not overlap another Lean proof job. `AGLIB_VERIFY_DIR` selects a verification root for resuming the same recorded basis.

The [GitHub Actions workflow](../.github/workflows/ci.yml) records the CI runner, prerequisite tools and resource profile. After guarded cache setup and cache validation it runs:

```sh
bash scripts/check.sh --rehash --ci
```

| Verification stage | Default local route | CI `--ci` route |
| --- | --- | --- |
| Production, positive-test and audit-support build; tests | Included | Included |
| Declaration lint, source style, explicit axiom audit | Included | Included |
| Negative controls and exact compiled inventory | Included | Included |
| Independent downstream build and audit | Included | Included |
| Extra independent library and client kernel replay | Included | Omitted; required locally before publication |

`--ci` skips only the two extra `check_kernel.py` calls. Lean itself kernel-checks theorem proofs when compiling them; those compiler checks remain part of the build. The separate independent replay is a local prepublication requirement.

CI uses the configured Batteries Lean linter through `lake lint -- --no-build`, followed by `lake exe mathlib/lint-style Aglib AglibTest`. These are the standard Lake interfaces to the pinned Lean implementations. The local route runs the same pinned declaration and style implementations without writing executable outputs into shared dependency caches. Python checks cover package structure, enrollment and execution; the axiom/origin audit is a separate Lean check. See [linter entry points](../scripts/README.md#check-entry-points) for the coverage and cache boundary.

## Memory and exact replay

The build helper runs one compiler process at a time; `AGLIB_BUILD_THREADS` selects its internal parallelism, otherwise inheriting `LEAN_NUM_THREADS` or using the conservative default. Exact kernel replay uses bounded batches in one monitored process; select their size with `AGLIB_KERNEL_BATCH_SIZE` or `--batch-size`. Batches that reach the RSS cutoff are retried at smaller sizes. A temporary toolchain wrapper applies the selected native `-j` and `-M` limits to direct and Lake-spawned frontends. The RSS watchdog sums the owned process group's memory, fails closed on monitoring, memory or concurrency failure, and signals only PIDs whose owned-group identity it rechecks. Native heap limits alone do not bound all mapped memory.

`AGLIB_LEAN_MEMORY_MB` and `AGLIB_RSS_LIMIT_MB` are in MiB. Choose values appropriate to the host, keeping the native Lean limit below the owned-group RSS cutoff. The helpers validate their settings; the workflow is the authority for CI's configured profile. Do not run another Lean job alongside this route.

Use [check_kernel.py](../scripts/check_kernel.py) for exact current-module replay, including server/private artifacts. It reuses the pinned installed `LeanChecker.replayFromImports` concurrently for a bounded set of exact enrolled modules. The default `leanchecker` CLI expands module prefixes and fans out concurrent jobs; use the maintained exact checker for whole-library replay.

```sh
python3 scripts/check_kernel.py --receipt-dir .lake/verification/kernel
python3 scripts/check_kernel.py --root examples/downstream --client \
  --receipt-dir .lake/verification/client-kernel
```

Run these after the corresponding build and audits, or use the full local route. `--only MODULE` is a diagnostic probe and cannot establish complete coverage. Resume only with the same source, artifact, configuration and installed-checker basis; a changed basis requires a fresh receipt directory. Historical receipts are not current verification evidence.

## Incremental cache and publication

The project cache covers the root and downstream build directories. Only the top-level package `version` in each root/client TOML file is omitted from semantic configuration hashing. All other configuration fields and executable `lakefile.lean` bytes remain significant. Source changes retain unaffected outputs through Lake `--rehash`; same-ABI dependency, option and other configuration changes retain reusable artifacts while Lake invalidates affected work. Changed, missing or unrecognized compiler stamps reset the owned build roots, and obsolete or renamed module outputs are pruned. Dependencies remain outside those owned roots. See [incremental cache details](../scripts/README.md#incremental-ci-build-cache).

A cache hit does not replace current tests, audits, inventory checks or the required local replay, and never makes a historical verification receipt current. Package version bumps preserve incremental CI reuse without accepting stale proof artifacts.

The publication target is the private repository `kangxyz/aglib`. Complete the full local route, including both independent kernel replays and the downstream audit, before publishing the verified source snapshot. The configured workflow and the commands above are procedures; current results belong in [WORK_PLAN.md](WORK_PLAN.md).

[generate_imports.py](../scripts/generate_imports.py) owns aggregate imports. The generator owner updates enrollment; `python3 scripts/generate_imports.py --check` detects drift. Modern `module` headers, precise `public import` and exposed public sections define the consumer/reduction boundary. [AglibTest](../AglibTest) and [examples/downstream](../examples/downstream) remain consumers, with rejection controls outside production imports.

Lean's default `maxHeartbeats` is 200000, and Mathlib uses that default. An override of `maxHeartbeats` or `synthInstance.maxHeartbeats` must be declaration-local (`set_option ... in`) and followed by a comment explaining why it is needed. The pinned [style linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Style.lean#L78) requires local scope, and the [heartbeat-comment linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean#L103) requires the explanation. A documented local value `0` is allowed; this library imposes no additional finite-positive restriction. Measure a declaration with `#count_heartbeats in` and leave headroom; Mathlib's [counting guide](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Util/CountHeartbeats.lean) suggests a sufficient budget of the form `2^k * 200000`.

Preserve contributor/license headers and exact source correspondence. Update the family guide when an object, namespace, hypothesis, result or canonical map changes.

A build checks elaboration, an audit checks covered foundation dependencies, and kernel replay checks compiled terms on its recorded current basis. None supplies an explicit mathematical theorem-family parameter or independently establishes an external proof chain. [WORK_PLAN.md](WORK_PLAN.md) records actual integration coverage.
