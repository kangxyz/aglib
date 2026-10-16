# Aglib scripts and extraction support

Run these tools from the package root. Production Lean modules do not depend on
`scripts/`. The project/package and Lean module root are `Aglib`; the repository directory slug is
`aglib`. The pinned Lean toolchain and dependency revisions belong to
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Check entry points

`check.sh --source-only` verifies generated enrollment, source layout, proof-token
policy, scoped heartbeat modifications with explanatory comments, and the Python regression suite. Run it
on a settled source tree; implementation authors and import generation share a
serial integration boundary.

`check.sh` additionally builds the production and positive test roots, replays
linters and explicit origin audits, exercises isolated rejection controls, checks
the compiled inventory, kernel-replays current project modules, and builds the
independent downstream client. `--rehash` is forwarded to the project build/test
commands. Every failed stage stops dependent stages.

.github/workflows/ci.yml runs the source-only entry before installing the
`lean-toolchain` selection through pinned elan. It separately caches third-party
`.lake/packages`, keyed by `lean-toolchain` and `lake-manifest.json`, and fetches
matching Mathlib proof artifacts with `lake exe cache get` under the owned-group
RSS guard. Checkout/cache action revisions and the elan release follow the authoritative Quillen CI framework.
The hosted `bash scripts/check.sh --rehash --ci` route runs after cache setup.
It omits only the two additional independent kernel replays. Production and test
compilation, declaration/style lint, axiom audits, controls, inventory, and the
independent downstream build and audit remain required. Default local `check.sh`
also performs both independent kernel replays before publication.

CI invokes the configured Batteries declaration linter and Mathlib's Lean style
driver through their native Lake interfaces, from the Aglib package root:

```sh
lake lint -- --no-build
lake exe mathlib/lint-style Aglib AglibTest
```

The first command includes Lake's configured builtin phase and then runs the
Batteries driver selected in `lakefile.toml`. The driver selects declarations by
defining-module origin, so native mathematical namespaces do not reduce package
coverage. Its `--no-build` rejects missing imported library artifacts; Lake can
still build the executable's tool prerequisites. The style driver reads Aglib's
current-root configuration and receives the explicit `Aglib AglibTest` selection.
Neither command replaces the separate Lean axiom/origin audit. Python checks
package structure, import enrollment and execution; it does not implement these
Lean declaration or text-style rules.

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

## Resource limits and exact kernel replay

Full checks serialize frontend processes. Normal builds can select internal
parallelism through `AGLIB_BUILD_THREADS`; without it, they inherit
`LEAN_NUM_THREADS` or use the conservative default. The count must be positive
and fit the available logical CPUs. A temporary toolchain wrapper carries the
same count to native `-j` and `LEAN_NUM_THREADS`, including Lake-spawned compilers,
while retaining the memory limits and one compiler process.
The wrapper links the installed toolchain read-only and changes no source or
proof options. `build_serial.py` first checks whether all targets are cached;
otherwise it invokes one ordinary Lake build graph for the requested targets.
Lake resolves and schedules the dependency graph once, with its parent worker
limited to one and compiler children receiving the requested internal parallelism.
The pinned Lake has no `-j` or maximum-jobs CLI flag.

The no-build probe writes its full output to `cached-check.log` and prints one
cache-hit or cache-miss summary. Only pinned Lake's exit code 3 accompanied
exclusively by its expected out-of-date errors permits a build fallback. Other
probe errors are printed and stop the run. Compiler failures remain visible in
the ordinary build output. Each receipt directory owns one probe log and refuses
to overwrite prior evidence.

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
search is performed. The default full-check timestamp directories remain fresh;
select a stable directory explicitly for incremental replay:

```sh
python3 scripts/check_kernel.py --receipt-dir .lake/verification/kernel
```

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

During development, build changed leaves and affected clients. When a scoped
replay is warranted, continue it through the explicit lineage. Integration and publication retain
full current library/client coverage and all other required checks. Matching
per-closure replay evidence discharges unchanged replay coverage; a probe alone
cannot discharge the full-publication requirement.

Do not run another Lean job concurrently with this serialized route. On restricted
macOS hosts, process monitoring and owned-process signaling require the authorized
unsandboxed execution route; monitoring failure cannot count as success.

## Incremental CI build cache

[Native caching](../doc/CACHING.md) owns the canonical `.github/actions/lake-cache` action and adjacent adapter. Its native toolchain cache retains artifacts and input mappings across manifest/option changes; public cache prerelease assets deliver upstream builds without cross-repository credentials. `build_serial.py --outputs FILE` forwards native Lake `-o` on both its no-build probe and ordinary build. Existing checkout cache behavior below remains additional incremental storage.

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
still validates compiler stamps and prunes obsolete modules before the current
`--rehash --ci` checks; partial caches do not establish verification.
Source changes can reuse unaffected compiled modules through Lake `--rehash`.

The official proof-cache command uses `resource_guard.py --bootstrap-cache`,
which accepts only `lake exe cache get`. This bootstrap mode keeps the same RSS
cutoff and one worker thread while allowing the cache tool's compiler children.
The CI runner and resource profile are defined in `.github/workflows/ci.yml`.
Its explicit `check.sh --rehash --ci` mode retains
compilation, linters, axiom audits, and downstream checks; the extra independent
root/client kernel replays remain in the default full local check before publication.

`prepare_build_cache.py` runs before any restored project olean is consumed.
Each build root carries a `.aglib-cache.json` stamp with its actual `lean
--version` identity and semantic configuration digest. The root stamp uses root
configuration; the client stamp includes both packages because it imports Aglib.
Missing, malformed, or compiler/toolchain-incompatible stamps clear only that
package's build root. Incompatible Lean binaries are discarded, never reused
across compiler versions. Same-ABI dependency/option changes retain artifacts and
traces for Lake `--rehash` to invalidate the affected imports and build arguments;
the semantic configuration digest is refreshed in the stamp. A compatible stamp
retains current module outputs and prunes obsolete facets in
`lib/lean` and `ir`, including old roots, deleted/renamed modules, auditor outputs,
and negative controls excluded from the positive enrollment. Root enrollment uses
`library_sources.py` production/positive lists plus `AglibTest/AuditSupport.lean`;
client enrollment uses its own current Lean source list. Redirected build paths
or symlinked build contents fail before cache mutation. Dependency sources and
caches remain outside these owned build roots.

`test_ci_cache.py` uses isolated temporary fixtures (`/private/tmp` on macOS) to cover configuration
identity, compatible reuse, incompatible reset, enrollment pruning, path guards,
and workflow ordering. Caches never replace audits, rejection controls, strict
compiled inventory, or kernel replay: every trust stage still runs in the full
`--rehash` checker.

## Maintained tools

| File | Interface and consumer |
| --- | --- |
| `resource_guard.py` | Samples only its owned process group's RSS; enforces one active Lean and closes the group on failure. `--capped-toolchain` supplies native compiler caps; the restricted `--bootstrap-cache` exception keeps the RSS limit. |
| `build_serial.py` | Checks cached targets first, then invokes one Lake build graph with one capped compiler process. |
| `check_kernel.py` | Replays bounded batches of the exact current production, positive-test, and audit-support inventory using installed `LeanChecker.replayFromImports`; writes resumable source/artifact-bound coverage receipts. `--client` checks the independent Consumer package. |
| `test_resource_guard.py` | Pure Python budget, fail-closed monitoring, exit propagation, and owned-PID termination regressions. |
| `test_kernel.py` | Exact enrollment, bounded task barrier, failed-batch rejection, RSS backoff, immutable attempt logs, and basis-checked legacy adoption regressions. |
| `test_build_serial.py` | Checks target validation, single-graph scheduling, strict cache-miss fallback, preserved probe logs, and compiler-wrapper argument caps using a small Python executable. |
| `check.sh` | Serialized source/full integration entry point; accepts `--source-only` and `--rehash`. |
| `library_sources.py` | Shared Lean lexical/import scanner and production, positive, audit, and downstream source inventories. `--style-sources --root PATH` prints module/path pairs. |
| `generate_imports.py` | Discovers occupied implementations and generates enrolled root/family facades. `--check` reports drift without writing; `--root PATH` selects a checkout. Exact generated markers control facade ownership. |
| `check_library_layout.py` | Checks enrollment, modern exports, exact local import resolution, forbidden application imports, and cycles. The exact generic DerivedCategory/HomotopyCategory `Plus` paths denote bounded-below categories and retain admission; plus-construction application families remain forbidden. Accepts `--root PATH`. |
| `check_placeholders.py` | Rejects proof placeholders/custom-axiom tokens outside isolated negative controls; comments and strings are masked. Accepts `--root PATH`. |
| `check_source_policy.py` | Follows pinned Mathlib: any option with a `maxHeartbeats` name component, including `synthInstance.maxHeartbeats`, must be scoped to one declaration with an explanatory comment after `in`. Documented local `0` is permitted. Other fixed source safety remains enforced; comment quality and budget necessity remain author judgments. Accepts `--root PATH`. |
| `check_compiled_inventory.py` | Matches the root-owned compiled replay view to current source; rejects deleted/old-prefix artifacts and negative controls in the positive view. Accepts `--root PATH`. |
| `check_negative_controls.py` | Compiles isolated control data in a temporary overlay and requires the specific imported/current-module axiom rejection. Setup errors cannot count as rejection. |
| `run_style_linter.py` | Runs the exact pinned style driver through a temporary optional-module overlay. `--check-prerequisites --sysroot PATH` inspects direct driver/source prerequisites without Lake, compilation, or writes. |
| `prepare_downstream.py` | Prepares the independently configured client's manifest and dependency-cache link from the pinned root manifest. It preserves the root manifest and existing dependency sources. |
| `migration_helpers.py` | Read-only transitional inspection of initial-extraction routing and namespace maps. `read_source` requires an explicit source root, exact Git revision, and exact source SHA-256; `write_source` and `record` are retired and always fail before writes. It is not the redesigned-source authoring pipeline or a production dependency. |
| `test_check_script.py` | Fixed command-level regressions for failure propagation, native CI and immutable-cache-safe local linter dispatch, explicit audits, and scoped kernel replay. |
| `test_integration_setup.py` | Regressions for exact compiled enrollment, isolated downstream manifest setup, and read-only optional linter prerequisite planning. |
| `test_migration_helpers.py` | Regressions for explicit source selection, revision/hash guards, preserved provenance identities, and retired writer failure without module/metadata mutation. |
| `test_source_guards.py` | Regression fixtures for lexical boundaries, facade ownership/enrollment, cycles, modern exports, placeholders, downstream imports, and local heartbeat policy. |

`__pycache__` is transient Python bytecode produced by execution and excluded from
source delivery. No cache, binary, or compiled Lean output belongs in a source
commit. If additional top-level files are maintained here, document their exact
backtick-enclosed names: Mathlib's `linter.allScriptsDocumented` checks these
mentions when enabled.


The initial extraction helper has no implicit machine-path source checkout. To
inspect a source, explicitly pass the directory containing its original `Quillen/`
or `R5Lab/` tree and both expected identities to `read_source`. For current LOCAL
Quillen work, the accepted revision is `189a8e779f0c68b2dfc6f8195daebb3e684a5905`;
the original `8362957` initial-extraction revision remains historical provenance.
The caller selects the checkout location and exact file hash. Returned `source_*`
fields describe those guarded original bytes. Existing provenance and current
native maps are untouched. Pure text projections are inspection aids and do not
select admissible mathematics; maintained redesigned files must be authored
through their current owner rather than replaying this helper.

Lean's default `maxHeartbeats` remains 200000, matching the pinned Mathlib lakefile's
choice not to override it. The option-name component rule also covers
`synthInstance.maxHeartbeats`; it does not impose a separate prohibition on local
`0`. A comment before the option alone does not replace the comment after `in`
required by the pinned deprecated-syntax linter. This infrastructure change does
not introduce or increase a production proof budget.

## Evidence boundary

The legacy `AglibTest/Axioms.lean` replay selects production declarations by
module origin, including private/generated declarations. Positive fixtures have a
separate generated entry; auditors and negative controls are excluded from it.
The allowed axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

`check_kernel.py` performs exact-module kernel replay under the pinned implementation;
source guards, linters, and axiom inventories are separate checks. None of them
discharges explicit mathematical theorem premises. After a source move, remove or
quarantine only this package's stale build view before kernel replay; dependency
sources and caches retain their own ownership.
