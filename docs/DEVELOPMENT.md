# Development and checks

Run commands from the package root. [lean-toolchain](../lean-toolchain) pins Lean 4.34.1; [lakefile.toml](../lakefile.toml) pins Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and declares `Aglib` and `AglibTest`. Keep the pinned [lake-manifest.json](../lake-manifest.json). Production imports use Mathlib and precise lower `Aglib` leaves.

## Normal task

Use the prepared workspace: encode/prove, compile the exact changed leaf, and
repair from its diagnostics. For example:

```sh
lake build Aglib.CategoryTheory.ExactCategory.Basic
```

At meaningful final code delivery, run the selected check once:
`python3 -m lean_ci check --config .github/lean-ci.toml --root . --requested-base ACCEPTED_COMMIT`. Reuse completed
categories after a failure through the [direct repair commands](#local-verification-and-ci).
Use a consumer only for a concrete interface question. Look up setup, cache or
environment details below only when a required input is missing or invalid.
Mathematical adoption uses the separate [scoped replay recipe](#kernel-replay-at-mathematical-adoption).

## Setup and focused builds

Consult this section only for an actual setup or artifact gap. Restore the
selected dependency/cache closure through the common tooling distribution:

```sh
python3 -m lean_ci prepare --config .github/lean-ci.toml --root .
```

Use `--requested-base REF` or `--target MODULE` for the intended incremental scope.
Preparation preserves matching compiled outputs; it does not establish checker
success. The shared workflow supplies the same preparation and cache policy.

Keep writable dependency build caches owned by this checkout. Before building with dependency links into another checkout, prepare private copies; ordinary Lake builds may compile missing dependency modules. Preserve the original sources and caches when making those copies.

All normal workflows must use only incremental checks, including authoring, maintenance, documentation, review, merge, integration and publication. Preserve trusted caches, reuse compatible build and trust evidence, reconcile combined changes and fill actual coverage gaps. Reconcile exact source/toolchain/configuration identities and obtain matching caches before building genuinely missing or changed required targets and needed affected consumers. Complete coherent mathematical obligations using focused compilation and repair where they advance the proof, with a focused `lake build` invocation:

See the exact-leaf command in the [normal task recipe](#normal-task).

The common checker owns guarded final-check execution and resource limits. Direct
focused Lake builds remain the authoring loop in a prepared workspace; they do not
establish separate lint, audit or mathematical-adoption coverage.

Incremental validation includes compilation, applicable declaration and text/style lint, affected `AglibTest` regression/property modules and downstream client tests, and source/import/enrollment or trust checks affected by the change. During development, use incremental compilation and its diagnostics, keeping compiler-integrated checks enabled. Independent lint and tests run only in the task's final validation before delivery; a helper return, internal commit or merge does not start that phase. Cover applicable categories there using matching prior evidence and focused new checks. Compilation covers only the lint or tests it actually runs. After final-check repairs, rerun only failed or newly affected checks. Documentation-only changes use applicable source/link checks and changed examples; unchanged behavior needs no new tests.

An API smoke check answers a concrete interface question; it is not a required follow-up to every theorem. The final-validation timing above governs independent lint and tests; do not interrupt authoring with per-helper or per-theorem smoke, axiom, lint, Python-test, diagnostic-probe or receipt chains. When tooling changes, include its affected regressions in final validation, selecting the affected test class where sufficient.

## Local verification and CI

Aglib uses the same config-only common checker as downstream libraries:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root .
python3 -m lean_ci check --config .github/lean-ci.toml --root . --requested-base ACCEPTED_COMMIT
```

[`.github/lean-ci.toml`](../.github/lean-ci.toml) declares `Aglib` production,
`AglibTest` positive Tests, tooling support and the independent downstream
`Consumer` package. Install the immutable `lean-incremental-ci` tooling release
selected by the reusable workflow, independently of mathematical dependency pins.
The consumer supplies no Python selection, task, binding or bootstrap adapter.

Selection follows affected consumers over the union of old and new import edges,
including deletion/rename identities. Build only current changed/missing required
modules. The standard profile retains source/link/layout/placeholder and budget
checks, source style, builtin lint, exact defining-origin declaration lint,
selected compile-time Tests/client proofs, axiom checks and private/generated
inventory controls. No whole-library umbrella is needed merely for lint or
metadata. Declaration lint uses a canonical isolated environment per origin,
importing `Batteries.Tactic.Lint` before the origin with fixed private visibility
and the native linter options/trust setting. Older umbrella or target-first lint
receipts are not equivalent to this predicate. Axiom checks retain their separate
kernel trust and allowed-foundation policy.

`AglibTest/Axioms.lean` and the client `Audit.lean` remain explicit-only exhaustive
mathematical audit entrypoints. `AuditSupport` and isolated compile-pass control
data remain enrolled; negative audit sources require their exact diagnostic,
not just any nonzero exit. Positive `AuditCoverage` data retains the foreign-name,
private and generated declaration cases. Ordinary selected-origin trust coverage
does not claim equivalence with a legacy whole-origin audit.

Use external `--state PATH` and `--progress PATH` to keep compatible individual
successes after repair. Repeat the same common entry; each result binds the actual
checker, source/import closure, compiler/runtime and relevant policy inputs.
A failed or interrupted peer cannot erase valid successes. Incompatible new
predicates start uncovered, while compatible compilation artifacts remain usable.
Initialization retains current unfinished obligations across subsequent heads.
A missing receipt requires uncovered checks; API failure remains an error, and
neither event requests a blanket rebuild.

Hosted CI delegates `plan`, `source`, `native`, `finalize`, preparation and cache
transport to one pinned reusable workflow. Source/preflight is independent from
long native work. Finalization aggregates existing results and correspondence
without executing checkers again; only qualified complete coverage can establish
a native baseline or publish a complete-coverage cache. Compiled artifacts and
per-check progress use separate compatibility boundaries. See [CI](CI.md) and
[cache semantics](CACHING.md) for their evidence and trust limits.

Ordinary code acceptance and cache publication do not request additional kernel
replay or claim mathematical acceptance. The adoption recipe below remains an
explicit separate consumer of the retained kernel checker.

## Memory and exact replay

The common kernel-adoption helper retains its guarded compiler profile. Exact replay uses
bounded batches in one monitored process, selected with `LEAN_CI_REPLAY_BATCH_SIZE` (legacy `AGLIB_KERNEL_BATCH_SIZE` remains accepted)
or `--batch-size`, and retries RSS-limited batches at smaller sizes. Its temporary
compiler wrapper applies native thread and heap caps. The RSS watchdog monitors
only its owned process group and rechecks identities before signaling. Common CI
instead uses its centrally derived host or admitted remote resource profile.

`AGLIB_LEAN_MEMORY_MB` and `AGLIB_RSS_LIMIT_MB` are in MiB. Choose values appropriate to the host, keeping the native Lean limit below the owned-group RSS cutoff. The common runtime validates its settings; the workflow supplies the CI resource profile. Do not run another Lean job alongside this route.

### Kernel replay at mathematical adoption

Formal mathematical acceptance here means the existing substantive adoption
milestone for claimed formalized results. It is not a new workflow state and
is not triggered by a commit, merge, ordinary code final check, cache publication,
writing review or exposé status review by itself. Keep the mathematical review
and status obligations appropriate to the actual product.

At that adoption, use the common `lean_ci replay` entry incrementally
for the accepted modules and required uncovered dependencies, retaining compatible
module-bound replay evidence from the stable root/client lineages. For example:

```sh
python3 -m lean_ci replay --root . --config .github/lean-ci.toml --receipt-dir .lake/verification/kernel \
  --modules Aglib.CategoryTheory.ExactCategory.Basic
python3 -m lean_ci replay --root . --config .github/lean-ci.toml --workspace downstream \
  --receipt-dir .lake/verification/client-kernel --modules Consumer.FundamentalGroup
```

Choose actual adopted modules; a scoped result does not establish whole-library
coverage. The checker labels `--modules` output as a probe and does not freshly
replay imported proofs. Combine its exact module evidence with compatible prior
coverage, filling the actual missing dependency coverage rather than replaying
unchanged accepted libraries. Use the same receipt directories across related
source changes so matching compiled-import evidence can be reused.

Replay supplies an additional kernel/environment check on recorded compiled
terms and artifacts. For unreviewed generated source or uncertain environments
and artifacts, resolve the source, options and trust basis and include the needed
scoped replay before adopting the mathematical result; an ordinary successful
compile or cached artifact alone is insufficient adoption evidence. Replay does
not replace mathematical correspondence/review or explicit theorem premises.
The pinned installed `LeanChecker.replayFromImports` implementation, resource
bounds and fail-closed compatibility checks remain unchanged. Whole-library
replay belongs only to explicitly requested diagnostics or warranted fault
recovery, through the existing comprehensive route.

On resumption, adopt the accepted operational tool revision separately from the frozen mathematical source snapshot, recording both identities. Continue the same explicit compatible kernel-receipt lineage; adopting operational guidance alone requires no new replay. Tool changes that affect the recorded compiler/runtime or checker semantics must satisfy the checker's compatibility rules before evidence can be reused.

Managed remote replay retains the admitted `R5_LEAN_REMOTE_PROFILE` wrapper and
its `LEAN_SYSROOT` overlay for import metadata extraction and replay. The checker
independently resolves the source `lean-toolchain` pin through Elan and requires
the reported physical prefix and overlay library to identify that same backend.
Managed evidence binds the backend, wrapper, profile and Elan locator. Changes
to those inputs require compatible fresh scoped evidence. Unmanaged execution
retains its strict executable/prefix identity check and existing closure keys.
Keep the owned phase's wrapper and resource profile set throughout the check;
selecting its physical backend directly would bypass the admitted resource guard.

The checker captures full identities at start/end and guards exact inputs and search-resolution candidates between batches, including ctime to detect changed-and-restored files. Missing dependency source metadata prevents reuse; incomplete compiled metadata or corrupt selected evidence fails closed. Original bases, records, logs and resource profiles remain immutable; current coverage summaries reference the original evidence and distinguish reuse from fresh execution. Older receipts without dependency metadata require a new closure-bound replay. [Replay mechanics](../scripts/README.md#resource-limits-and-exact-kernel-replay) describe the evidence layout and configuration normalization.

## Incremental cache and publication

[Native caching](CACHING.md) owns shared toolchain artifacts, cross-checkout and cross-library reuse, public CI cache release assets, and the reusable producer/consumer protocol. Package options retain ordinary `.lake/build` files for existing audits. Mathlib keeps `lake exe cache get`. The checkout caches below additionally preserve incremental partial progress.

The project cache covers the root and downstream build directories. The top-level package `version`, `enableArtifactCache` and `restoreAllArtifacts` in each root/client TOML file are omitted from semantic configuration hashing; these storage-policy flags preserve pre-migration cache keys. All other configuration fields and executable `lakefile.lean` bytes remain significant. The `.aglib-cache.json` wrapper stamp is advisory provenance, not proof of each output's compiler identity. Missing, malformed, schema-mismatched or compiler/toolchain/configuration-mismatched wrapper metadata preserves outputs. Lake's current input/output traces and matching artifact cache select reusable outputs and rebuild only the actual affected closure through `--rehash`; obsolete owned module outputs are pruned. Diagnosed corrupt or untrustworthy native data requires separate scoped fault recovery. Dependencies remain outside those owned roots. See [incremental cache details](../scripts/README.md#incremental-ci-build-cache).

CI uses explicit cache restore and save steps. Newly acquired dependency proof caches are saved after the matching fetch succeeds, before the project check. Project outputs are eligible for saving even when a later check fails, provided restoration supplied a primary key and compiler/cache preparation succeeded. Immutable project-cache generations include the GitHub run ID and attempt, so identical-source retries can preserve further build progress. Restoration tries the same source and configuration first, then the same configuration, then the same OS and architecture. Restored outputs undergo obsolete-module pruning and native Lake `--rehash` trace validation; wrapper stamps do not validate or invalidate all outputs.

Main-branch CI runs serialize without cancelling the active run, allowing eligible build progress to be saved before the next snapshot starts. GitHub keeps the latest pending snapshot in that group. Other branches and pull-request refs cancel superseded active runs. See [workflow concurrency](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/control-workflow-concurrency).

A build-cache hit alone does not establish tests, audits, inventory checks or replay required at mathematical acceptance. Retain compatible evidence for each required check and fill only actual gaps. The replay controller can discharge unchanged modules with validated matching per-closure evidence from the explicitly selected lineage; a historical receipt alone supplies no current coverage. Package version bumps preserve incremental CI reuse without accepting stale proof artifacts.

The publication target is the public repository [`kangxyz/aglib`](https://github.com/kangxyz/aglib). Before publishing, reconcile applicable code-check and downstream-audit coverage for the combined source snapshot, using compatible retained evidence and narrow new checks. Publication of code or cache artifacts alone does not trigger replay. When publication also adopts a substantive mathematical result, complete its [mathematical acceptance](#memory-and-exact-replay), including scoped library/client replay where applicable. The configured workflow and the commands above are procedures; current results belong in [WORK_PLAN.md](WORK_PLAN.md).

The common `lean_ci imports` command owns configured aggregate maintenance.
`python3 -m lean_ci imports --config .github/lean-ci.toml --root . --check` detects
drift; use `--write` for guarded updates after mathematical source changes. Modern `module` headers, precise `public import` and exposed public sections define the consumer/reduction boundary. [AglibTest](../AglibTest) and [examples/downstream](../examples/downstream) remain consumers, with rejection controls outside production imports.

Lean's default `maxHeartbeats` is 200000, and Mathlib uses that default. An override of any option with an exact `maxHeartbeats` name component, including `synthInstance.maxHeartbeats`, must use a positive finite budget in a declaration-local scope (`set_option ... in`), with a comment after `in` explaining why it is needed. The pinned [style linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Style.lean#L78) requires local scope, and the [heartbeat-comment linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean#L103) requires the explanation. Aglib additionally forbids `0`, which means unlimited, even with a valid local explanation; this numeric restriction is stricter than pinned Mathlib. Measure a declaration with `#count_heartbeats in` and leave headroom; Mathlib's [counting guide](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Util/CountHeartbeats.lean) suggests a sufficient budget of the form `2^k * 200000`.

## Contribution conventions

Keep maintained text, identifiers, comments and documentation in English. Follow Mathlib source style and the [naming conventions](NAMING.md). Use the pinned Lean and Mathlib versions; dependency changes require their own coordinated update.

Current source author headers credit `kangxyz`. Credit actual contributors when they contribute; do not enforce a permanent single-author list or add blanket tool attribution. Preserve copyright and Apache 2.0 license notices. Keep historical source identities and correspondence in [REFERENCES.md](REFERENCES.md) and the existing migration records; current author credit does not erase provenance.

Update the owning family README when an object, namespace, hypothesis, result or canonical map changes. Keep cross-family architecture, development and provenance in `docs/`. New families need an admitted object or result and a current consumer, rather than empty scaffolding.

Preserve foreign changes and exact write ownership. Inspect `HEAD` and worktree status before writing and before staging or committing; coordinate overlapping edits and shared build outputs. Keep Git index and `HEAD` mutations serial. Do not push without an explicit current request.

Use incremental checks during development, integration and publication. Preserve applicable enrollment, import direction, source policy, tests, linters, axiom coverage, rejection controls, inventory and downstream coverage through compatible evidence and actual gap checks. At a mathematical-adoption milestone, reuse the explicit replay lineage and cover its affected modules; a narrow probe does not claim whole-library coverage. Build success does not discharge mathematical premises.

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
  arithmetic and K-theory applications keep their downstream owners. General
  Milnor K-theory is an admitted algebraic family; its application comparisons
  remain downstream. Being
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

The two paths specify the candidate convention; create mathematical
subdirectories and source facades only when real candidate modules need them.
A temporary location does not itself assert upstream acceptance or a completed
migration.
