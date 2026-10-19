# Development and checks

Run commands from the package root. [lean-toolchain](../lean-toolchain) pins Lean 4.34.1; [lakefile.toml](../lakefile.toml) pins Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and declares `Aglib` and `AglibTest`. Keep the pinned [lake-manifest.json](../lake-manifest.json). Production imports use Mathlib and precise lower `Aglib` leaves.

## Normal task

Use the prepared workspace: encode/prove, compile the exact changed leaf, and
repair from its diagnostics. For example:

```sh
python3 scripts/build_serial.py --receipt-dir .lake/verification/iteration-001 \
  Aglib.CategoryTheory.ExactCategory.Basic
```

At meaningful final code delivery, run the selected check once:
`bash scripts/check.sh --base ACCEPTED_COMMIT --rehash`. Reuse completed
categories after a failure through the [direct repair commands](#local-verification-and-ci).
Use a consumer only for a concrete interface question. Look up setup, cache or
environment details below only when a required input is missing or invalid.
Mathematical adoption uses the separate [scoped replay recipe](#kernel-replay-at-mathematical-adoption).

## Setup and focused builds

Consult this section only for an actual setup or artifact gap. Prefer the
[selected cache route](../scripts/README.md#incremental-ci-build-cache) for required
imports. The retained comprehensive bootstrap is for explicitly assigned broad
dependency-cache recovery:

```sh
python3 scripts/resource_guard.py --bootstrap-cache \
  --receipt .lake/verification/cache-bootstrap.json -- lake exe cache get
```

The bootstrap mode accepts only that exact cache command. It retains the process-group RSS cutoff and capped compiler threads while allowing the cache tool's compiler children. Normal project proof work uses the sequential route.

Keep writable dependency build caches owned by this checkout. Before building with dependency links into another checkout, prepare private copies; ordinary Lake builds may compile missing dependency modules. Preserve the original sources and caches when making those copies.

All normal workflows must use only incremental checks, including authoring, maintenance, documentation, review, merge, integration and publication. Preserve trusted caches, reuse compatible build and trust evidence, reconcile combined changes and fill actual coverage gaps. Reconcile exact source/toolchain/configuration identities and obtain matching caches before building genuinely missing or changed required targets and needed affected consumers. Complete coherent mathematical obligations using focused compilation and repair where they advance the proof, with [build_serial.py](../scripts/build_serial.py):

See the exact-leaf command in the [normal task recipe](#normal-task).

Choose a fresh build receipt directory for each invocation; the helper refuses
to overwrite its prior `cached-check.log`.

The helper accepts `--root ROOT`, `--rehash`, optional native Lake `--outputs FILE` mappings and one or more module targets. It first checks whether the requested targets are already cached, then invokes one ordinary Lake build graph for missing work. Lake schedules dependencies with one capped Lean compiler process at a time; `AGLIB_BUILD_THREADS` selects that compiler's internal parallelism. Expected out-of-date diagnostics from the cache probe are saved in `cached-check.log`; configuration, tool and compilation failures still fail the check. [resource_guard.py](../scripts/resource_guard.py) supplies the same owned-group guard for other commands through `--capped-toolchain --receipt FILE -- COMMAND`. [scripts/README.md](../scripts/README.md) owns detailed runtime and helper interfaces.

Incremental validation includes compilation, applicable declaration and text/style lint, affected `AglibTest` regression/property modules and downstream client tests, and source/import/enrollment or trust checks affected by the change. During development, use incremental compilation and its diagnostics, keeping compiler-integrated checks enabled. Independent lint and tests run only in the task's final validation before delivery; a helper return, internal commit or merge does not start that phase. Cover applicable categories there using matching prior evidence and focused new checks. Compilation covers only the lint or tests it actually runs. After final-check repairs, rerun only failed or newly affected checks. Documentation-only changes use applicable source/link checks and changed examples; unchanged behavior needs no new tests.

An API smoke check answers a concrete interface question; it is not a required follow-up to every theorem. The final-validation timing above governs independent lint and tests; do not interrupt authoring with per-helper or per-theorem smoke, axiom, lint, Python-test, diagnostic-probe or receipt chains. When tooling changes, include its affected regressions in final validation, selecting the affected test class where sufficient.

## Local verification and CI

Normal local and CI validation selects the changed providers and their actual
import-graph consumers from an explicit accepted Git baseline:

```sh
bash scripts/check.sh --base ACCEPTED_COMMIT --rehash
```

The default includes tracked and untracked working-tree changes. Add `--head HEAD`
for a clean committed snapshot. Missing baselines, configuration/pin changes and
unrecognized paths fail with a scope decision required; none selects a full build.
Markdown and documentation-evidence JSON changes run static source and local-link
checks only. They do not install Lean, compile, lint, run tests or publish caches.
Tooling changes run their Python fixture regressions without requiring Lean.

The [standalone CI core](CI.md) owns its plan, execution records and mandatory
final coverage decision. It chooses an ancestor with completed native validation through
[`ci_baseline.py`](../scripts/ci_baseline.py), rather than the previous push.
Failed or cancelled runs and green source-only runs do not advance this
baseline. Unverified proof changes therefore remain in the next affected plan,
including after a scripts-only repair. The selector rejects the earlier unsafe
incremental workflow and unavailable validation history; it never silently
substitutes the previous push or a full build. A manual comparison may move the
verified baseline earlier, but cannot skip forward over unchecked changes.

This comparison baseline does not discard partial build progress. Matching
compiled outputs from failed runs remain eligible for the existing native and
project cache restoration, and Lake validates them before reuse. Individual
builtin/declaration lint and selected audit successes have separate progress
records bound to their validated native inputs, outputs and checker policy.
Those records never authorize skipping current native graph validation.

The local final native phase compiles changed providers, runs their pinned declaration
and text/style linters, then builds affected consumers, positive tests and the
independent client. Import-only facades remain compiled consumers when affected.
Their unrelated imports must pass a cache-only check before the facade build:
recover compatible cached outputs if that check fails. A broad import facade
never silently starts compiling unrelated cold siblings. Unchanged facades and
unrelated proof modules are not selected merely for convenience.

Native CI uses a shared guarded Lake `--rehash` build for the complete current
library and positive-test root graph after cache preparation, then consumes its
validated identities for selected independent checks. A cache-only preflight
prevents unrelated cold imports from silently triggering broad recovery. A final
current-root barrier and the core finalizer reject missing graph or check coverage.
Lake decides which compilation work is stale; a Git difference cannot replace
that decision. Successful partial checks remain reusable under their exact input
bindings, while failed or incompatible records select real execution.

Selected-origin axiom auditing reuses `AglibTest.AuditSupport`, including its
private/generated-declaration inventory and fixed allowed axioms. Negative
controls and selected compiled enrollment remain separate checks; stale or negative
outputs still fail. The existing client origin audit runs for affected clients.
Proof-only edits retain matching rejection-control evidence from the accepted
baseline. Controls rerun when their fixtures, auditor/support policy, pinned
configuration or compiler-wrapper runtime change, or for explicit `--full`
diagnostics. If matching baseline control coverage is unavailable, run
`python3 scripts/check_negative_controls.py` for that actual gap. Selected-origin
axiom auditing still covers changed proofs independently of this reuse.
Ordinary selected final checks, commits and merges do not request extra kernel
replay. They report their applicable code/trust evidence; mathematical adoption
uses the [incremental replay recipe](#kernel-replay-at-mathematical-adoption).
A normal cache export records replay as not requested and externally tracked;
it does not claim formal mathematical acceptance or full inventory coverage.

Use `AGLIB_VERIFY_DIR` for a fresh run directory. After a repair, rerun only failed
or newly affected categories with `--phase providers`, `--phase provider-lint`,
`--phase consumers`, `--phase trust` or `--phase client`; repeat `--phase` to combine
categories. A `--native-only` repair reuses already completed static/tooling
checks. These repair runs do not export a complete selected-validation mapping.
Retain their compatible prior coverage rather than rerunning unchanged checks.

For a single failed module, existing direct commands narrow the repair further
(replace `MODULE` and use a fresh build `DIR`):

```sh
# Provider lint failure, after compiling any repaired source:
lake --no-build lint --builtin-only MODULE
python3 scripts/run_declaration_linter.py MODULE
python3 scripts/run_style_linter.py --modules MODULE
# Late test failure: build just that test, then use its name in the lint commands above.
python3 scripts/build_serial.py --receipt-dir DIR AglibTest.MODULE
# Late client failure:
python3 scripts/build_serial.py --root examples/downstream --receipt-dir DIR Consumer.MODULE
# From examples/downstream, preserve the client's existing audit boundary:
cd examples/downstream
lake --no-build build Consumer
lake env lean -j1 Audit.lean
```

Complete still-affected selected trust checks with the existing `--phase trust`
command; completed provider lint need not repeat. Reselect if the actual import
closure changes.

Whole-library diagnostics require an explicit `--full`:

```sh
bash scripts/check.sh --full --source-only
bash scripts/check.sh --full --rehash
```

These commands retain the comprehensive source/tooling suite and full local
kernel replay. They are separately requested diagnostics, never an automatic
fallback for missing caches or coverage. Coordinate all native checks with other
Lean jobs; they write shared build outputs and remain serialized.

The [workflow](../.github/workflows/ci.yml) invokes the core's `plan`, `source`,
`native` and `finalize` operations. The plan precedes native setup; the finalizer
is required even for source-only coverage. Matching caches are restored for
native scopes, including compatible individual-check progress. An optional manual
comparison can only move the automatically verified baseline earlier. Native exports use mappings emitted by
successfully completed selected build phases; export schedules no new build.
The adjacent `.coverage.json` records affected-only coverage and selected target
identities. CI logs and retained evidence distinguish this from whole-library
validation. Pinned declaration/style implementations, Lake builtin lint, compiler-integrated
linters, source policy, origin audits and rejection controls remain enabled.
Batteries declaration lint filters the pinned driver enumeration to exact selected
defining-module origins, preserving all enabled checks. Affected consumers are
linted after compilation, without repeating provider or unrelated imported-origin
coverage; text/style lint selects changed files only. Builtin lint uses explicit
compiled implementation modules and `--no-build`;
import-only facades receive compilation and exact source-style checks. CI prepares
only the named imports of the pinned linter runtimes in its writable dependency
caches when needed. Local runtime execution preserves shared dependency caches.
The uploaded native staging tree includes `validation-coverage.json`; client-only
changes produce no new root-package native publication. New-branch push events
use an available default-branch merge-base, or the empty tree for a genuinely
parentless initial commit; unresolved Git metadata still fails actionably.

## Memory and exact replay

The build helper runs one compiler process at a time; `AGLIB_BUILD_THREADS` selects its internal parallelism, otherwise inheriting `LEAN_NUM_THREADS` or defaulting to one. The native `check.sh` route sets `LEAN_NUM_THREADS=1`, so only `AGLIB_BUILD_THREADS` overrides its compiler-thread default. Exact kernel replay uses bounded batches in one monitored process; select their size with `AGLIB_KERNEL_BATCH_SIZE` or `--batch-size`. Batches that reach the RSS cutoff are retried at smaller sizes. A temporary toolchain wrapper applies the selected native `-j` and `-M` limits to direct and Lake-spawned frontends. The RSS watchdog sums the owned process group's memory, fails closed on monitoring, memory or concurrency failure, and signals only PIDs whose owned-group identity it rechecks. Native heap limits alone do not bound all mapped memory.

`AGLIB_LEAN_MEMORY_MB` and `AGLIB_RSS_LIMIT_MB` are in MiB. Choose values appropriate to the host, keeping the native Lean limit below the owned-group RSS cutoff. The helpers validate their settings; the workflow is the authority for CI's configured profile. Do not run another Lean job alongside this route.

### Kernel replay at mathematical adoption

Formal mathematical acceptance here means the existing substantive adoption
milestone for claimed formalized results. It is not a new workflow state and
is not triggered by a commit, merge, ordinary code final check, cache publication,
writing review or exposé status review by itself. Keep the mathematical review
and status obligations appropriate to the actual product.

At that adoption, use [check_kernel.py](../scripts/check_kernel.py) incrementally
for the accepted modules and required uncovered dependencies, retaining compatible
module-bound replay evidence from the stable root/client lineages. For example:

```sh
python3 scripts/check_kernel.py --receipt-dir .lake/verification/kernel \
  --modules Aglib.CategoryTheory.ExactCategory.Basic
python3 scripts/check_kernel.py --root examples/downstream --client \
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

The checker captures full identities at start/end and guards exact inputs and search-resolution candidates between batches, including ctime to detect changed-and-restored files. Missing dependency source metadata prevents reuse; incomplete compiled metadata or corrupt selected evidence fails closed. Original bases, records, logs and resource profiles remain immutable; current coverage summaries reference the original evidence and distinguish reuse from fresh execution. Older receipts without dependency metadata require a new closure-bound replay. [Replay mechanics](../scripts/README.md#resource-limits-and-exact-kernel-replay) describe the evidence layout and configuration normalization.

## Incremental cache and publication

[Native caching](CACHING.md) owns shared toolchain artifacts, cross-checkout and cross-library reuse, public CI cache release assets, and the reusable producer/consumer protocol. Package options retain ordinary `.lake/build` files for existing audits. Mathlib keeps `lake exe cache get`. The checkout caches below additionally preserve incremental partial progress.

The project cache covers the root and downstream build directories. The top-level package `version`, `enableArtifactCache` and `restoreAllArtifacts` in each root/client TOML file are omitted from semantic configuration hashing; these storage-policy flags preserve pre-migration cache keys. All other configuration fields and executable `lakefile.lean` bytes remain significant. The `.aglib-cache.json` wrapper stamp is advisory provenance, not proof of each output's compiler identity. Missing, malformed, schema-mismatched or compiler/toolchain/configuration-mismatched wrapper metadata preserves outputs. Lake's current input/output traces and matching artifact cache select reusable outputs and rebuild only the actual affected closure through `--rehash`; obsolete owned module outputs are pruned. Diagnosed corrupt or untrustworthy native data requires separate scoped fault recovery. Dependencies remain outside those owned roots. See [incremental cache details](../scripts/README.md#incremental-ci-build-cache).

CI uses explicit cache restore and save steps. Newly acquired dependency proof caches are saved after the matching fetch succeeds, before the project check. Project outputs are eligible for saving even when a later check fails, provided restoration supplied a primary key and compiler/cache preparation succeeded. Immutable project-cache generations include the GitHub run ID and attempt, so identical-source retries can preserve further build progress. Restoration tries the same source and configuration first, then the same configuration, then the same OS and architecture. Restored outputs undergo obsolete-module pruning and native Lake `--rehash` trace validation; wrapper stamps do not validate or invalidate all outputs.

Main-branch CI runs serialize without cancelling the active run, allowing eligible build progress to be saved before the next snapshot starts. GitHub keeps the latest pending snapshot in that group. Other branches and pull-request refs cancel superseded active runs. See [workflow concurrency](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/control-workflow-concurrency).

A build-cache hit alone does not establish tests, audits, inventory checks or replay required at mathematical acceptance. Retain compatible evidence for each required check and fill only actual gaps. The replay controller can discharge unchanged modules with validated matching per-closure evidence from the explicitly selected lineage; a historical receipt alone supplies no current coverage. Package version bumps preserve incremental CI reuse without accepting stale proof artifacts.

The publication target is the public repository [`kangxyz/aglib`](https://github.com/kangxyz/aglib). Before publishing, reconcile applicable code-check and downstream-audit coverage for the combined source snapshot, using compatible retained evidence and narrow new checks. Publication of code or cache artifacts alone does not trigger replay. When publication also adopts a substantive mathematical result, complete its [mathematical acceptance](#memory-and-exact-replay), including scoped library/client replay where applicable. The configured workflow and the commands above are procedures; current results belong in [WORK_PLAN.md](WORK_PLAN.md).

[generate_imports.py](../scripts/generate_imports.py) owns aggregate imports. The generator owner updates enrollment; `python3 scripts/generate_imports.py --check` detects drift. Modern `module` headers, precise `public import` and exposed public sections define the consumer/reduction boundary. [AglibTest](../AglibTest) and [examples/downstream](../examples/downstream) remain consumers, with rejection controls outside production imports.

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
