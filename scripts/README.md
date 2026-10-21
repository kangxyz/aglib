# Aglib scripts and extraction support

Run these tools from the package root. Production Lean modules do not depend on
`scripts/`. The project/package and Lean module root are `Aglib`; the repository directory slug is
`aglib`. The pinned Lean toolchain and dependency revisions belong to
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Check entry points

Normal final validation uses `bash scripts/check.sh --base ACCEPTED_COMMIT --rehash`.
The default includes working-tree changes; `--head HEAD` requires a clean committed
snapshot. `affected_scope.py` selects changed providers and affected consumers
using the existing Lean import scanner, with old changed/deleted imports retained
for rename/delete closure. The JSON plan binds the Git baseline, checked HEAD,
selected sources and configuration bytes. Missing bases, pin/configuration changes
and unknown paths fail closed instead of selecting full roots.

`check_affected.py` is the local entry to Aglib's shared recipe and executor.
It selects observed working-tree inputs, runs cheap source/link checks and
applicable Python fixtures, validates one native graph, then runs the declared
native/batch lint and relevant in-package test groups. Markdown and documentation-evidence JSON changes
stop after static checks, without native setup or publication. Unrelated imports
must pass a cache-only preflight before affected facades or umbrella checks can
consume them; a missing cache does not authorize unrelated cold compilation.

Production builtin/declaration lint retains the complete `Aglib` environment.
An existing `AglibTest.lean` retains its umbrella check. When that entry is
absent, selected positive test origins use one batch invocation of
`run_declaration_linter.py`. The pinned Batteries driver retains a separate
linter environment per origin, all enabled checks, nolints handling and failure
behavior; only repeated frontend initialization is removed. The same helper
checks selected `AuditSupport` and `Tools.*` origins. Full selection includes all
positive tests. These actual modes remain distinct in check compatibility.

`run_style_linter.py --modules MODULE ...` retains the pinned Mathlib options,
`lintModules`, naming and script-documentation checks with exact source
selection. Its enumeration adapter fails on unrecognized driver text; the
no-argument helper retains comprehensive driver behavior. Neither helper
overwrites dependency caches.

Routine formalization does not automatically add additional trust, inventory,
negative-control or downstream preparation/build/audit tasks. Kernel replay is
an explicitly requested standalone diagnostic only, including at mathematical
adoption. This applies equally to merge, publication and full-library scope.
Complex multi-stage repeat-acceptance chains are prohibited; independent
mathematical and writing review obligations are unchanged.

For repairs, use `--phase providers`, `--phase provider-lint` or
`--phase consumers` (repeatable), optionally `--native-only`, and retain the same
external `AGLIB_VERIFY_DIR` for compatible successes. Explicitly requested
`--phase trust` and `--phase client` retain their diagnostic behavior. Only an
explicit client request requires client preparation and matching metadata.

`check.sh --full [--source-only] [--rehash] [--ci]` selects the whole library and
in-package tests through the same shared executor and compatible progress. Without literal `--full`, `check.sh` requires an
incremental baseline or guarded `--plan FILE`; no absent cache, manual dispatch,
unknown path or changed pin implicitly selects the comprehensive command. All-zero
new-branch event bases use an available trusted default-branch merge-base or a
genuine parentless initial-tree diff; unavailable Git metadata fails actionably.

The public [CI caller](../.github/workflows/ci.yml) uses the shared native
[workflow](../.github/workflows/lean-ci.yml); see [CI and local checks](../docs/CI.md).
The installable [lean-incremental-ci package](../ci/README.md) serves local checks
and retained committed-adapter consumers. For the retained committed adapter,
planning precedes Lean installation and cache restoration. Its `ci_baseline.py`
selects an ancestor whose native validation
completed under an exact reviewed workflow and implementation recipe. The legacy
whole-library witness is restricted to its reviewed source commit. A failed run,
a source-only green run and the former previous-push
incremental protocol cannot advance this baseline. Missing history fails closed.
The selector records the source commit and supporting run; affected selection
prints its base, head and module counts. A manual comparison may only select an
ancestor of the verified baseline. Failed-run compiled caches retain their
existing reuse path. `ci_state.py` separately retains input-bound individual
check successes through `lean_ci.state`; compiled-artifact reuse alone never
supplies that evidence. `library_sources.py` retains Aglib inventory policy and
re-exports the shared `lean_ci.source` parser. Generic package code has no Aglib
imports or fixed resource-variable names.

The CI adapter explicitly assigns complete current check coverage for pin,
compiler and build-configuration changes. The local affected checker still
requires its caller's explicit scope decision for those changes. Downstream metadata preparation is separate and explicitly requested. Restoring artifacts for the new inputs before
Lake's `--rehash`/`--no-build` validation can avoid target recompilation. This does
not assume cross-compiler compatibility; [caching](../docs/CACHING.md#upstream-and-toolchain-updates)
describes the supported boundary.

`ci/native_test.py` is an explicitly requested standalone diagnostic. Its
isolated two-module producer/consumer fixture exercises partial success,
matching native cache restoration and rejection of stale upstream inputs.
The [initial policy cutover](../docs/CI.md#initial-policy-cutover) records the
actual legacy predicates retained for unchanged origins separately from current
selected checks. Semantic predicate changes need assigned coverage and cannot
inherit arbitrary earlier lint successes.

Markdown/evidence-only plans never enter native or cache
steps. Native CI runs selected checks with `--outputs FILE`; successful build-phase
mappings are concatenated only after all selected checks succeed. No export build
or implicit root target is added. The adjacent `.coverage.json` records the base,
HEAD, actual selected targets and affected-only coverage. CI packages it as
`validation-coverage.json`; client-only changes do not publish root-package mappings. Single-phase repairs do
not export a complete selected-validation mapping. Cache misses preserve native
outputs and fill only required selected work; cold broad-facade siblings require
matching-cache recovery. The pinned toolchain, manifests and resource limits stay
under their existing owners.

Selected builtin lints run in a fresh guarded process per module. The declaration
wrapper likewise uses a separate Lean interpreter per exact defining-module origin,
so imported environments do not accumulate across targets. Successful provider
compilation is reused when rerunning a failed lint category.

### Separately requested whole-library diagnostics

The following commands describe `check.sh --full`; normal local and CI checks
continue to use the affected plan above.

Separately requested whole-library CI diagnostics run Lake's configured builtin lint phase and Mathlib's Lean style driver
through their native Lake interfaces, and the Batteries declaration linter from
its pinned source, from the Aglib package root, each as its own guarded process:

```sh
lake lint --builtin-only
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Aglib
lake exe mathlib/lint-style Aglib AglibTest
```

A single `lake lint -- --no-build` would run the builtin phase and then the
Batteries driver selected in `lakefile.toml` while the builtin phase's environment
stays mapped; their combined resident memory exceeds the CI budget
([performance guide](../docs/PERFORMANCE.md#declaration-lint-memory-in-ci)). The driver selects declarations by
defining-module origin, so native mathematical namespaces do not reduce package
coverage. Its `--no-build` rejects missing imported library artifacts; Lake can
still build the executable's tool prerequisites. The style driver reads Aglib's
current-root configuration and receives the explicit `Aglib AglibTest` selection.
Full scope runs the same basic build/lint/in-package test categories. It does not
request replay, additional inventory/control chains or separate client validation.
Existing selected-origin axiom auditing retains its ordinary final-validation
predicate and compatible evidence under
[mathematical trust](../docs/DEVELOPMENT.md#mathematical-trust).
The standalone diagnostic tools below remain available when specifically
requested. Matching caches and completed checks are reused across repairs.

The local route preserves shared dependency caches by running the same pinned
Batteries source directly:

```sh
python3 scripts/resource_guard.py --capped-toolchain --receipt .lake/verification/declaration-lint.json -- lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Aglib
```

`--no-build` rejects missing project or linter oleans instead of rebuilding
dependency caches.

`run_style_linter.py` executes the pinned Mathlib
`scripts/lint-style.lean` with the arguments `Aglib AglibTest`:

```sh
python3 scripts/resource_guard.py --capped-toolchain --receipt .lake/verification/style.json -- python3 scripts/run_style_linter.py
```

If `Cli.Basic` or `ImportGraph.Imports.FromSource` is absent, the helper compiles
only those exact source modules into a temporary runtime overlay. Their imported
prerequisites must already be cached. The overlay is removed afterward; no
cached namespace sibling is hidden: its artifacts are linked read-only into the
overlay, and compilation refuses to overwrite a cached artifact. No
executable or output is built in an immutable dependency checkout. The helper
also compiles the byte-identical driver into the overlay, then runs an import-only
shim with the pinned Lake shared library loaded. This initializes driver options
before evaluation and makes Lake's native workspace loader available.
The actual checks and arguments remain those of the pinned driver. The helper
does not pass `--fix`. CI owns writable dependency caches and uses the native
commands above instead of this local overlay.

## Resource limits and explicitly requested kernel replay

The replay mechanics in this section apply only to an explicitly requested
standalone diagnostic; routine formalization never schedules them.

Full checks serialize frontend processes. Normal builds can select internal
parallelism through `AGLIB_BUILD_THREADS`; without it, they inherit
`LEAN_NUM_THREADS` or default to one. Every `check.sh` scope inherits the same
configured resource limits; use `AGLIB_BUILD_THREADS` for compiler parallelism.
The count must be positive
and fit the available logical CPUs. A temporary toolchain wrapper carries the
same count to native `-j` and `LEAN_NUM_THREADS`, including Lake-spawned compilers,
while retaining the memory limits and one compiler process.
The wrapper links the installed toolchain read-only and changes no source or
proof options. `build_serial.py` first checks whether all targets are cached;
otherwise it invokes one ordinary Lake build graph for the requested targets.
Lake resolves and schedules the dependency graph once, with its parent worker
limited to one and compiler children receiving the requested internal parallelism.
The pinned Lake has no `-j` or maximum-jobs CLI flag.

`resource_guard.py --capped-toolchain` uses the same selected child-thread count
and keeps the parent `LEAN_NUM_THREADS=1`. It binds the absolute capped compiler
for direct `lean ARGUMENTS` and `lake env lean ARGUMENTS` commands, including an
absolute Lake launcher and an optional `/usr/bin/time -lp` prefix. This binding
is necessary because Lake's augmented `PATH` can bypass a bare wrapper name.
Arguments after `lean` are preserved. Other Lake commands retain their native
compiler selection. Unsupported direct Lake-env, timing, absolute-Lean, shell
and `env` wrapper forms fail before launch rather than being interpreted.
Other launcher programs remain RSS/concurrency guarded; indirect children that
recompute executable paths, including the local Python style launcher, need
their own explicit native-cap binding. A capped `PATH` alone is not evidence
that such nested frontend commands received native thread or memory flags.
The guard receipt records `native_build_threads` separately from the one-thread
parent and the one-active-frontend bound. The exact cache bootstrap exception
retains one child thread and its existing fanout/RSS policy.

The no-build probe writes its full output to `cached-check.log` and prints one
cache-hit or cache-miss summary. Only pinned Lake's exit code 3 accompanied
exclusively by its expected out-of-date errors permits a build fallback. Other
probe errors are printed and stop the run. Compiler failures remain visible in
the ordinary build output. Each build receipt directory owns one probe log and refuses
to overwrite prior evidence. Use a fresh build receipt directory for each invocation;
this differs from the explicitly resumable kernel-replay directory below.
`AGLIB_VERIFY_DIR` selects the comprehensive checker's output root, not a resume
mechanism for the entire checker.

`AGLIB_LEAN_MEMORY_MB` and `AGLIB_RSS_LIMIT_MB` configure the native allocation
limit and aggregate owned-group RSS cutoff in MiB. Defaults are conservative and
depend on physical RAM. Overrides are validated against an OS reserve and the
host's RAM ceiling, and the native limit must be smaller than the RSS cutoff. Choose a
profile appropriate to the execution host; the hosted profile is maintained in
`.github/workflows/ci.yml`. The watchdog samples every 0.1 seconds,
fails before launching work if monitoring is unavailable, and signals only
positive PIDs whose process-group identity it rechecks. It terminates on memory,
concurrency, or monitoring failure and records peak RSS and process closure.
Exact `--githash` and `--print-prefix` locator actions, with only the injected
resource flags, do not count as compiler jobs; their RSS is still included.
Files, `--run`, setup files, and other actions receive no such exemption.
Native memory limits do not bound all mapped memory, so the RSS guard remains
required. No address-space limit is used.

The pinned `leanchecker` executable launches every selected module concurrently.
`check_kernel.py` instead imports the installed `LeanChecker` module and calls
only `replayFromImports` for bounded batches of exact modules. Each fresh process
runs at most the selected number of tasks; the next batch starts after it exits.
`--batch-size` or `AGLIB_KERNEL_BATCH_SIZE` selects a positive bound that fits the
available logical CPUs. It never executes imported `main` or requests fresh replay
of imported proofs. Exported, server, and private parts are inspected; a module is
recorded as vacuous only when its last, most private part contains no new constants.
All tasks must succeed before any module success is accepted. An RSS-cutoff failure
retries smaller batches; proof, monitoring, malformed-output, and other failures
stop the check. Full coverage still requires the complete unique current inventory;
`--only` and `--modules` are diagnostic probes. Each module's evidence binds its
actual compiled import closure to source and exported/server/private/IR artifacts,
effective configuration, the installed compiler/runtime and checker, and exact
replay semantics. A single guarded metadata pass reads compiled import arrays;
it does not replay imported proofs. The graph is shared, dependency keys are
memoized, and module mappings are released after copying their import names.

Reuse is explicit: select the same receipt directory across adjacent source
snapshots, or relocate that directory with its coherent checkout. Unrelated
module edits and enrollment changes retain matching evidence; changed imported
source or artifacts invalidate dependents even if their own `.olean` is unchanged.
Missing source metadata disables reuse for the affected closure; incomplete
compiled metadata fails closed. Configuration uses the existing typed cache
normalization (ignoring only package version and storage-policy fields); raw
configuration hashes remain in the full provenance. No historical-directory
search is performed. For an explicitly requested replay diagnostic, select a
stable receipt directory:

```sh
python3 scripts/check_kernel.py --receipt-dir .lake/verification/kernel \
  --modules Aglib.CategoryTheory.ExactCategory.Basic
python3 scripts/check_kernel.py --root examples/downstream --client \
  --receipt-dir .lake/verification/client-kernel --modules Consumer.FundamentalGroup
```

Replay adds a recorded kernel/environment diagnostic and does not replace
mathematical review or explicit premises. Mathematical adoption does not require
or automatically schedule this diagnostic.

The pinned replay core checks each module's declarations sequentially; bounded
module tasks provide replay parallelism. Normal-build thread settings remain
separate from the replay batch setting. Original bases, module records, logs and
resource profiles remain immutable. Changed full bases live under
`snapshots/<basis-hash>/`; the current coverage/probe summaries point to each
module's original record and report reused counts without relabeling execution.
Only these selected summaries and the initial basis are consulted. Full content
identities are captured at start and end; between batches, exact input/facet and
namespace-resolution metadata guards include inode and ctime, rejecting even
changed-and-restored files. An initial compiled-tree stat sweep fences metadata
extraction; it is not repeated per batch. Concurrent source/build activity may
conservatively invalidate a run.

Explicit `--adopt-legacy` migration also requires the full frozen source basis
and the recognized prior runner through `--legacy-source-basis` and
`--legacy-runner`. It validates prior success records and preserves their raw
evidence and execution profiles. Older receipts lack dependency metadata and
require a new closure-bound replay before automatic reuse. Missing or corrupted
selected records, original bases, logs or resource evidence fail closed.

On an explicitly requested replay resumption, distinguish the operational tool
revision from the mathematical source snapshot and reuse compatible evidence.
A scoped probe does not claim complete-library replay or mathematical acceptance.
Merge, publication and adoption do not request replay or client diagnostics.

Do not run another Lean job concurrently with this serialized route. On restricted
macOS hosts, process monitoring and owned-process signaling require the authorized
unsandboxed execution route; monitoring failure cannot count as success.

## Incremental CI build cache

[Native caching](../docs/CACHING.md) owns the canonical `.github/actions/lake-cache` action and adjacent adapter. Its native toolchain cache retains artifacts and input mappings across manifest/option changes; public cache prerelease assets deliver upstream builds without cross-repository credentials. `build_serial.py --outputs FILE` forwards native Lake `-o` on both its no-build probe and ordinary build. Existing checkout cache behavior below remains additional incremental storage.

`cache_key.py` adapts the typed TOML normalization from Quillen's
`scripts/cache_key.py`. It hashes root and downstream toolchains, manifests,
TOML configuration, and any executable `lakefile.lean` bytes. The top-level
package `version`, `enableArtifactCache` and `restoreAllArtifacts` are omitted
from each TOML configuration; native storage-policy migration preserves the
existing schema and legacy keys. Types and array order
remain significant; missing or unusable configuration fails instead of returning
a partial key. Changing package versions or native storage policy therefore
preserves the configuration key. Dependency revisions, Lean options, and toolchains change it.

CI uses separate pinned `actions/cache/restore` and `actions/cache/save`
steps. The dependency cache retains its exact OS/architecture, toolchain
and manifest key. It is saved after matching Mathlib proof-cache acquisition
succeeds, before the long project check.

The project cache contains only `.lake/build` and
`examples/downstream/.lake/build`. Its save key combines OS, architecture,
configuration digest, the current root/test/downstream Lean source digest,
and the GitHub run ID and attempt. Cache entries are immutable; these
generations let identical-source retries save further partial progress.
Restore prefixes try the same source and configuration first, then the same
configuration, then another configuration on the same OS/architecture.
The first prefix also matches legacy exact-source keys without a generation.
Package-version-independent hashing remains unchanged.

The explicit project save uses `always()` but requires a primary key from
the restore step and successful compiler/cache preparation. It can therefore
preserve available build outputs after a later check fails. Restoration
still prunes obsolete modules before native Lake trace validation in the current
`--rehash --ci` checks; advisory stamps and partial caches do not establish verification.
Source changes can reuse unaffected compiled modules through Lake `--rehash`.

The selected proof-cache command is `python3 scripts/cache_ci.py --plan PLAN
--receipt RECEIPT`. It resolves the pinned dependencies, projects the existing
scope graph's actual provider/consumer/in-package-test imports (including required
broad facades) and named lint tooling to explicit Mathlib roots, then uses
the existing capped toolchain and RSS guard with serialized compiler launches
and exact cached compiler metadata queries. `affected_scope.py --cache-roots PLAN`
prints the same validated roots after dependency resolution. Markdown-only plans
skip dependency resolution and cache work; missing sources or basis fail without
an unscoped fetch. The stricter original `--bootstrap-cache` gate remains unchanged.
The CI runner and resource profile are defined in `.github/workflows/ci.yml`.
Local final checks require matching prepared root dependencies; client setup is
required only for an explicitly requested client diagnostic. Use an external
`AGLIB_VERIFY_DIR`; retries in that state reuse compatible completed checks.
The local entry and committed CI use the same `lean_ci.recipe` and task runner,
with different source/CI admission boundaries. Production and test declaration
lint use their accepted umbrella environments; old exact-origin successes do
not become umbrella coverage. A source-only scope performs no cache setup.
Its incremental `check.sh --base BASE --rehash --ci` mode runs basic source
checks, selected compilation, native lint and relevant in-package tests. Full
scope uses the same categories; no routine path adds replay or client checks.

`prepare_build_cache.py` runs before restored project outputs enter the declared
CI check. Each build root carries an advisory `.aglib-cache.json` provenance stamp
recording the current `lean --version` identity and semantic configuration digest;
it does not prove that every output matches that compiler. The root stamp uses root
configuration; the client stamp includes both packages because it imports Aglib.
Missing, malformed, schema-mismatched or compiler/toolchain/configuration-mismatched
wrapper metadata preserves outputs. Native Lake input/output traces bind compiler,
source, imports and options; `--rehash` and matching artifact caches select reusable
outputs and rebuild only the actual affected closure. Diagnosed corrupt or untrustworthy
native data requires separate scoped fault recovery. The helper refreshes advisory
provenance and prunes obsolete owned facets in
`lib/lean` and `ir`, including old roots, deleted/renamed modules, auditor outputs,
and negative controls excluded from the positive enrollment. Root enrollment uses
`library_sources.py` production/positive lists plus `AglibTest/AuditSupport.lean`;
client enrollment uses its own current Lean source list. Redirected build paths
or symlinked build contents fail before cache mutation. Dependency sources and
caches remain outside these owned build roots.

`test_ci_cache.py` uses isolated temporary fixtures (`/private/tmp` on macOS) to cover configuration
identity, preservation across wrapper-metadata changes, enrollment pruning, path guards,
and workflow ordering. Caches preserve progress; checks reuse only compatible
evidence for the selected routine categories.

## Maintained tools

| File | Interface and consumer |
| --- | --- |
| `resource_guard.py` | Samples only its owned process group's RSS; enforces one active Lean and closes the group on failure. `--capped-toolchain` supplies native compiler caps; the restricted `--bootstrap-cache` exception keeps the RSS limit. |
| `build_serial.py` | Checks cached targets first, then invokes one Lake build graph with one capped compiler process. |
| `check_kernel.py` | Replays bounded batches of the exact current production, positive-test, and audit-support inventory using installed `LeanChecker.replayFromImports`; writes resumable source/artifact-bound coverage receipts. `--client` checks the independent Consumer package. |
| `test_resource_guard.py` | Pure Python budget, fail-closed monitoring, exit propagation, and owned-PID termination regressions. |
| `test_kernel.py` | Exact enrollment, bounded task barrier, failed-batch rejection, RSS backoff, immutable attempt logs, and basis-checked legacy adoption regressions. |
| `test_build_serial.py` | Checks target validation, single-graph scheduling, strict cache-miss fallback, preserved probe logs, and compiler-wrapper argument caps using a small Python executable. |
| `check.sh` | Incremental final-check adapter; accepts `--base`/`--head`, guarded `--plan`, `--source-only`, `--native-only`, `--phase`, `--outputs`, `--rehash` and `--ci`. Comprehensive diagnostics require literal `--full`. |
| `affected_scope.py` | Pure-source Git/import-graph selector; accepts `--base`/`--head` or explicit `--full`, `--output` and `--github-output`. |
| `check_affected.py` | Thin dirty-worktree entry over the shared Aglib native recipe/executor; observes inputs before selection and preserves successful checks after later failures. |
| `test_affected_scope.py` | Small import/Git fixtures and mocked commands for changed providers, consumers, renames/deletes, fail-closed scope, lint ordering, documentation skips and export coverage. |
| `cache_ci.py` | Resolves validated affected-plan Mathlib roots and fetches their proof caches through the serialized capped toolchain and resource guard; source-only plans skip dependency and cache work. |
| `test_cache_ci.py` | Mocked checks for exact cache-root forwarding, source-only skips, and fail-closed rejection of missing scope or dependency inputs. |
| `ci_baseline.py` | Selects an ancestor with completed native CI validation, rejecting source-only greens and unsafe prior incremental runs; records the supporting run and constrains optional older manual bases. |
| `test_ci_baseline.py` | Checks failed/partial/static-only histories, versioned workflow eligibility, ancestry, manual-base safety, pagination and unavailable verification evidence without Lean or cache mutation. |
| `ci_pipeline.py` | Owns the CI plan, source/native execution records and mandatory final coverage decision; the workflow supplies environment and cache transport. |
| `test_ci_pipeline.py` | Regressions for verified scope, complete current graph coverage, skipped/incomplete phases, source drift and final-result integrity. |
| `test_ci_audit.py` | Fixed audit source admission and structured module-name argument validation, without running Lean. |
| `test_ci_integration.py` | Exercises real failed-proof/repair commit histories and public plan/source/finalize entry points, including missing native work, wrong-plan records and source drift, without running Lean. |
| `ci_state.py` | Stores compatible individual check successes bound to validated native inputs/outputs, checker policies and actual command receipts. |
| `test_ci_state.py` | Checks partial-progress reuse, input/checker changes, stale outputs, failed receipts and incompatible records. |
| `library_sources.py` | Shared Lean lexical/import scanner and production, positive, audit, and downstream source inventories. `--style-sources --root PATH` prints module/path pairs. |
| `generate_imports.py` | Discovers occupied implementations and generates enrolled root/family facades. `--check` reports drift without writing; `--root PATH` selects a checkout. Exact generated markers control facade ownership. The test-only umbrella uses legacy imports when composing legacy audit fixtures; production facades remain modern. |
| `check_library_layout.py` | Checks enrollment, modern exports, exact local import resolution, forbidden application imports, and cycles. The exact generic DerivedCategory/HomotopyCategory `Plus` paths denote bounded-below categories and retain admission; plus-construction application families remain forbidden. Accepts `--root PATH`. |
| `check_placeholders.py` | Rejects proof placeholders/custom-axiom tokens outside isolated negative controls; comments and strings are masked. Accepts `--root PATH`. |
| `check_source_policy.py` | Any option with an exact `maxHeartbeats` name component, including `synthInstance.maxHeartbeats`, must use a positive finite budget scoped to one declaration with an explanatory comment after `in`. Aglib rejects `0` (unlimited), including documented local zero budgets; this is stricter than pinned Mathlib. Copyright headers require nonempty author credits while original extraction notices are preserved. Other fixed source safety remains enforced; comment quality and budget necessity remain author judgments. Accepts `--root PATH`. |
| `check_compiled_inventory.py` | Matches the root-owned compiled replay view to current source; rejects deleted/old-prefix artifacts and negative controls in the positive view. Accepts `--root PATH`. |
| `check_negative_controls.py` | Compiles isolated control data in a temporary overlay and requires the specific imported/current-module axiom rejection. Setup errors cannot count as rejection. |
| `run_declaration_linter.py` | Exact-origin Batteries adapter for explicitly selected AuditSupport and Tools origins; leaf diagnostics do not replace ordinary umbrella validation. Never builds project or dependency modules. |
| `run_style_linter.py` | Runs the exact pinned style driver through a temporary optional-module overlay. `--check-prerequisites --sysroot PATH` inspects direct driver/source prerequisites without Lake, compilation, or writes. |
| `prepare_downstream.py` | Prepares the independently configured client's manifest and dependency-cache link from the pinned root manifest. It preserves the root manifest and existing dependency sources. |
| `migration_helpers.py` | Read-only transitional inspection of initial-extraction routing and namespace maps. `read_source` requires an explicit source root, exact Git revision, and exact source SHA-256; `write_source` and `record` are retired and always fail before writes. It is not the redesigned-source authoring pipeline or a production dependency. |
| `test_check_script.py` | Fixed command-level regressions for failure propagation, native CI and immutable-cache-safe local linter dispatch, explicit diagnostic separation. |
| `test_integration_setup.py` | Regressions for exact compiled enrollment, isolated downstream manifest setup, and read-only optional linter prerequisite planning. |
| `test_migration_helpers.py` | Regressions for explicit source selection, revision/hash guards, preserved provenance identities, and retired writer failure without module/metadata mutation. |
| `test_source_guards.py` | Regression fixtures for lexical boundaries, facade ownership/enrollment, cycles, modern exports, placeholders, downstream imports, mixed-format test umbrellas, author credits, and local heartbeat policy. |

`__pycache__` is transient Python bytecode produced by execution and excluded from
source delivery. No cache, binary, or compiled Lean output belongs in a source
commit. If additional top-level files are maintained here, document their exact
backtick-enclosed names: Mathlib's `linter.allScriptsDocumented` checks these
mentions when enabled.


The initial extraction helper has no implicit machine-path source checkout. To
inspect a source, explicitly pass the directory containing its original `Quillen/`
or `R5Lab/` tree and both expected identities to `read_source`. For the historical local
Quillen selection recorded by this extraction, the accepted revision was `189a8e779f0c68b2dfc6f8195daebb3e684a5905`;
the original `8362957` initial-extraction revision remains historical provenance.
The caller selects the checkout location and exact file hash. Returned `source_*`
fields describe those guarded original bytes. Existing provenance and current
native maps are untouched. Pure text projections are inspection aids and do not
select admissible mathematics; maintained redesigned files must be authored
through their current owner rather than replaying this helper.

Lean's default `maxHeartbeats` remains 200000, matching the pinned Mathlib lakefile's
choice not to override it. The option-name component rule also covers
`synthInstance.maxHeartbeats`. Aglib additionally requires positive finite budgets:
`0` means unlimited and is forbidden even in a documented local scope. A comment
before the option alone does not replace the comment after `in`
required by the pinned deprecated-syntax linter. This infrastructure change does
not introduce or increase a production proof budget.

## Evidence boundary

The legacy `Audits/Aglib.lean` replay selects production declarations by
module origin, including private/generated declarations. Positive fixtures have a
separate generated entry; auditors and negative controls are excluded from it.
The allowed axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

`check_kernel.py` performs exact-module kernel replay under the pinned implementation;
source guards, linters, and axiom inventories are separate checks. None of them
discharges explicit mathematical theorem premises. After a source move, prune
or quarantine obsolete owned module facets before
kernel replay, preserving current compatible outputs. Dependency sources and
caches retain their own ownership.
