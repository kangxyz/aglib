# Development and checks

Run commands from the package root. [lean-toolchain](../lean-toolchain) pins Lean 4.34.1; [lakefile.toml](../lakefile.toml) pins Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and declares `Aglib` and `AglibTest`. Keep the pinned [lake-manifest.json](../lake-manifest.json). Production imports use Mathlib and precise lower `Aglib` leaves.

## Setup and focused builds

Fetch matching official Mathlib artifacts through the maintained resource guard:

```sh
python3 scripts/resource_guard.py --bootstrap-cache \
  --receipt .lake/verification/cache-bootstrap.json -- lake exe cache get
```

The bootstrap mode accepts only that exact cache command. It retains the process-group RSS cutoff and capped compiler threads while allowing the cache tool's compiler children. Normal project proof work uses the sequential route.

Keep writable dependency build caches owned by this checkout. Before building with dependency links into another checkout, prepare private copies; ordinary Lake builds may compile missing dependency modules. Preserve the original sources and caches when making those copies.

Build a changed leaf and its affected consumers with [build_serial.py](../scripts/build_serial.py):

```sh
python3 scripts/build_serial.py --receipt-dir .lake/verification/iteration \
  Aglib.CategoryTheory.ExactCategory.Basic
```

The helper accepts `--root ROOT`, `--rehash`, optional native Lake `--outputs FILE` mappings and one or more module targets. It first checks whether the requested targets are already cached, then invokes one ordinary Lake build graph for missing work. Lake schedules dependencies with one capped Lean compiler process at a time; `AGLIB_BUILD_THREADS` selects that compiler's internal parallelism. Expected out-of-date diagnostics from the cache probe are saved in `cached-check.log`; configuration, tool and compilation failures still fail the check. [resource_guard.py](../scripts/resource_guard.py) supplies the same owned-group guard for other commands through `--capped-toolchain --receipt FILE -- COMMAND`. [scripts/README.md](../scripts/README.md) owns detailed runtime and helper interfaces.

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

Run these after the corresponding build and audits, or use the full local route. `--only MODULE` and `--modules MODULE ...` are diagnostic probes and cannot establish complete coverage. Select the same explicit receipt directory to continue scoped work across small source changes. Matching evidence is reused by each module's actual compiled import closure, including dependency source, exported/server/private/IR artifacts, effective configuration, compiler/runtime and checker semantics. An unrelated edit or new enrollment does not discard unaffected evidence; an imported source/artifact change invalidates its dependents. A coherent relocation can reuse matching evidence without rewriting the original execution provenance.

The checker captures full identities at start/end and guards exact inputs and search-resolution candidates between batches, including ctime to detect changed-and-restored files. Missing dependency source metadata prevents reuse; incomplete compiled metadata or corrupt selected evidence fails closed. Original bases, records, logs and resource profiles remain immutable; current coverage summaries reference the original evidence and distinguish reuse from fresh execution. Older receipts without dependency metadata require a new closure-bound replay. [Replay mechanics](../scripts/README.md#resource-limits-and-exact-kernel-replay) describe the evidence layout and configuration normalization.

## Incremental cache and publication

[Native caching](CACHING.md) owns shared toolchain artifacts, cross-checkout and cross-library reuse, public CI cache release assets, and the reusable producer/consumer protocol. Package options retain ordinary `.lake/build` files for existing audits. Mathlib keeps `lake exe cache get`. The checkout caches below additionally preserve incremental partial progress.

The project cache covers the root and downstream build directories. The top-level package `version`, `enableArtifactCache` and `restoreAllArtifacts` in each root/client TOML file are omitted from semantic configuration hashing; these storage-policy flags preserve pre-migration cache keys. All other configuration fields and executable `lakefile.lean` bytes remain significant. Source changes retain unaffected outputs through Lake `--rehash`; same-ABI dependency, option and other configuration changes retain reusable artifacts while Lake invalidates affected work. Changed, missing or unrecognized compiler stamps reset the owned build roots, and obsolete or renamed module outputs are pruned. Dependencies remain outside those owned roots. See [incremental cache details](../scripts/README.md#incremental-ci-build-cache).

CI uses explicit cache restore and save steps. Newly acquired dependency proof caches are saved after the matching fetch succeeds, before the project check. Project outputs are eligible for saving even when a later check fails, provided restoration supplied a primary key and compiler/cache preparation succeeded. Immutable project-cache generations include the GitHub run ID and attempt, so identical-source retries can preserve further build progress. Restoration tries the same source and configuration first, then the same configuration, then the same OS and architecture. Every restored project cache still undergoes compiler validation, obsolete-module pruning and Lake `--rehash` checks.

Main-branch CI runs serialize without cancelling the active run, allowing eligible build progress to be saved before the next snapshot starts. GitHub keeps the latest pending snapshot in that group. Other branches and pull-request refs cancel superseded active runs. See [workflow concurrency](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/control-workflow-concurrency).

A build-cache hit does not replace current tests, audits, inventory checks or required local replay coverage. The replay controller can discharge unchanged modules with validated matching per-closure evidence from the explicitly selected lineage; a historical receipt alone supplies no current coverage. Package version bumps preserve incremental CI reuse without accepting stale proof artifacts.

The publication target is the public repository [`kangxyz/aglib`](https://github.com/kangxyz/aglib). Complete the full local route, including both independent kernel replays and the downstream audit, before publishing the verified source snapshot. The configured workflow and the commands above are procedures; current results belong in [WORK_PLAN.md](WORK_PLAN.md).

[generate_imports.py](../scripts/generate_imports.py) owns aggregate imports. The generator owner updates enrollment; `python3 scripts/generate_imports.py --check` detects drift. Modern `module` headers, precise `public import` and exposed public sections define the consumer/reduction boundary. [AglibTest](../AglibTest) and [examples/downstream](../examples/downstream) remain consumers, with rejection controls outside production imports.

Lean's default `maxHeartbeats` is 200000, and Mathlib uses that default. An override of `maxHeartbeats` or `synthInstance.maxHeartbeats` must be declaration-local (`set_option ... in`) and followed by a comment explaining why it is needed. The pinned [style linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Style.lean#L78) requires local scope, and the [heartbeat-comment linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean#L103) requires the explanation. A documented local value `0` is allowed; this library imposes no additional finite-positive restriction. Measure a declaration with `#count_heartbeats in` and leave headroom; Mathlib's [counting guide](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Util/CountHeartbeats.lean) suggests a sufficient budget of the form `2^k * 200000`.

## Contribution conventions

Keep maintained text, identifiers, comments and documentation in English. Follow Mathlib source style and the [naming conventions](NAMING.md). Use the pinned Lean and Mathlib versions; dependency changes require their own coordinated update.

Current source author headers credit `kangxyz`. Credit actual contributors when they contribute; do not enforce a permanent single-author list or add blanket tool attribution. Preserve copyright and Apache 2.0 license notices. Keep historical source identities and correspondence in [REFERENCES.md](REFERENCES.md) and the existing migration records; current author credit does not erase provenance.

Update the owning family README when an object, namespace, hypothesis, result or canonical map changes. Keep cross-family architecture, development and provenance in `doc/`. New families need an admitted object or result and a current consumer, rather than empty scaffolding.

Preserve foreign changes and exact write ownership. Inspect `HEAD` and worktree status before writing and before staging or committing; coordinate overlapping edits and shared build outputs. Keep Git index and `HEAD` mutations serial. Do not push without an explicit current request.

During development build changed leaves and affected clients. When a scoped replay is warranted, continue it through the explicit receipt lineage. At integration and publication use the full route above for enrollment, import direction, source policy, tests, linters, axiom coverage, rejection controls, compiled inventory, downstream checks and complete required local replay coverage. Current matching per-closure evidence covers unchanged modules; diagnostic probes do not establish the full inventory. Build success does not discharge mathematical premises.

A build checks elaboration, an audit checks covered foundation dependencies, and kernel replay checks compiled terms on its recorded current basis. None supplies an explicit mathematical theorem-family parameter or independently establishes an external proof chain. [WORK_PLAN.md](WORK_PLAN.md) records actual integration coverage.

## Downstream candidates for Aglib

During downstream development, place a new reusable general-theory implementation
that belongs in Aglib in the host library's `Aglib/` subtree:

| Source package | Source directory | Temporary module prefix |
| --- | --- | --- |
| R5Lab | `lean/R5Lab/Aglib/` | `R5Lab.Aglib` |
| Quillen | `Quillen/Aglib/` | `Quillen.Aglib` |

These are ordinary checked source modules with a prospective upstream owner.
Do not create a package-root `Aglib/` source tree in a downstream package: it
would compete with the actual dependency's `Aglib.*` module identities.

- Search Mathlib and the pinned Aglib API first. Reuse or extend their actual
  objects and maps. A candidate must state general algebraic geometry or related
  mathematical theory under its full hypotheses. Curve, projective-line,
  arithmetic and K-theory applications keep their downstream owners; being
  useful in two applications alone does not select Aglib ownership.
- Mirror Aglib's mathematical hierarchy below the temporary prefix, following
  [architecture](ARCHITECTURE.md) and [naming](NAMING.md). Use native mathematical
  declaration namespaces from the start, such as `Algebra`, `CategoryTheory`,
  `CochainComplex` and `AlgebraicGeometry.Scheme`; the host prefix is a module
  location, not a declaration namespace. Do not add `R5Lab.Aglib`,
  `Quillen.Aglib` or `Aglib` wrappers around general declarations.
- Keep the candidate dependency closure general. Import focused Mathlib and
  Aglib leaves or explicitly designated candidate leaves, respecting the
  existing package dependency direction. Do not import ordinary host
  application modules. Isolate a required general prerequisite as a candidate
  first; keep application adapters outside the subtree. Coordinate one source
  owner when both downstream libraries need the same result.
- In each module docstring, name the intended `Aglib.*` module, describe the
  generality and actual hypotheses, and identify the current consumer. A
  family README records its interfaces and main mathematical results. A direct
  upstream contribution may skip the temporary location when it is already
  ready to integrate.
- Candidates use the host's normal source enrollment, Lean options, focused
  builds, lint and axiom policy. They are maintained proofs, not scratch or a
  place for placeholders. Put incomplete exploration outside production source.
  Add a focused client only for a meaningful uncovered interface condition.
- Move a ready, coherent candidate dependency group into Aglib, update its
  colocated guides and source provenance, obtain acceptance on the current
  identities, and then advance downstream pins. Retarget consumers to the
  upstream modules and remove the candidate implementation in the same
  downstream change. Preserve native declaration names when they still express
  the correct interface. Do not retain duplicate implementations or introduce
  a compatibility facade as the default migration route.

The two subtrees currently document this convention; create mathematical
subdirectories and source facades only when real candidate modules need them.
A temporary location does not itself assert upstream acceptance or a completed
migration.
