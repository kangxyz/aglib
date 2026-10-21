# Incremental CI contract

The reusable [lean-incremental-ci package](../ci/README.md) owns configuration,
selection, execution, check predicates, progress and final acceptance. Aglib uses
[declarative configuration](../.github/lean-ci.toml) and the same short reusable
workflow caller as its consumers. Tooling is pinned independently of mathematical
dependencies. A skipped workflow step cannot waive a required task or phase.

## Source, baseline and obligations

The common plan binds the current committed source, config/policy inputs and
actual executing implementation. Working-tree checks observe their own source
basis and remain distinct from committed CI evidence. Temporal guards cover
source bytes, path resolution, optional inputs, compiler/runtime and consumed
native artifacts; content compatibility does not depend on installation paths.

An accepted native baseline needs identifiable successful execution and actual
compatible coverage from an ancestor. Source-only green runs and previous pushes
do not supply it. Shared semantic-version-aware compatibility imports only old
predicates and input coverage that genuinely match. There is no consumer-specific
initial or repair-parent commit whitelist. Requested bases can only widen verified
selection. API failure remains an error rather than invented absent history.

Initialization constructs the current obligation universe and subtracts matching
individual successes and explicitly compatible inherited coverage. It retains
unfinished obligations across failed heads, reconciles changed or removed inputs
and preserves successful peers. A partial run cannot publish complete coverage.
New runtime-first exact-origin declaration lint is not equivalent to old umbrella
or target-first lint; those older results are not re-keyed as new successes.

## Incremental selection and checks

Compute reverse reachability over the union of old/new imports, retaining deleted
identities for selection but building only current modules. Package-qualified
Test/client graphs preserve their own source roots. Dependency/compiler/config
changes require actual old/new input assessment, not a guessed full-library build.
Compatible Lake artifacts remain available; unrelated cold closures are diagnosed
cache gaps. Lake owns compilation identities, hashes, build scheduling and native
staging, while the common runtime supplies resource caps.

The mandatory profile covers source/link/enrollment/layout/placeholder and budget
checks, source style, selected compilation, builtin lint, declaration lint,
compile-time positive Test/client checks, selected-origin axiom audit and
private/generated compiled inventory. Import-only facades remain enrolled and
compiled; a conservative declaration-free certificate can omit empty declaration
lint without expanding it to an umbrella check. Source style does not require a
subject's compiled closure. Selected tests execute through Lake and are not
elaborated a second time through a whole-Test replay.

Declaration lint has one fixed isolated environment per origin: runtime
`Batteries.Tactic.Lint` first, then that origin, with private visibility and the
pinned native driver's options and lint trust setting. Shared immutable runtime
import preparation must preserve this environment exactly. Enabled/slow/always
checks and nolints semantics remain those of the pinned driver. Axiom checks use
their separate kernel trust/visibility, actual defining origins and allowed
foundations `propext`, `Classical.choice`, and `Quot.sound`.

Aglib's legacy `AglibTest/Axioms.lean` and downstream `Audit.lean` remain enrolled
explicit-only mathematical audit entrypoints. `AuditSupport` and isolated imported
control data retain their roles; `AuditCoverage` is positive foreign-namespace,
private/generated data. The two expected-failure audits require their exact
unsupported-assumption diagnostics, with isolated compile-pass prerequisites.
A setup/import failure cannot count as rejection. Packaged generic checker controls
remain required independently of these retained library fixtures.

## Progress, finalization and cache trust

Only completed successful commands with valid resource receipts and a closed
owned process group establish individual success. Keys bind the checker predicate,
arguments, current source/native import closure, actual compiler/runtime,
relevant policy and environment. Reflective import metadata and ordered search
resolution retain private/meta and absence/shadow guards. Unsupported metadata
selects actual checking instead of invented reuse. Hash/metadata discovery may be
shared within protected intervals; current-input verification remains required.

Keep external `--state` and `--progress` paths after a failure. Later failed or
interrupted work preserves valid individual successes and compiled artifacts.
Finalization aggregates required existing results and correspondence; it schedules
no compiler or checker. Only qualified successful native coverage can establish a
baseline or publish complete-coverage artifacts. Exported root/client mappings
retain their workspace identity and narrow scope; exporting does not rebuild.

The common `prepare` entry and reusable workflow restore matching dependencies,
compiled outputs and separate check progress. PR/untrusted caches do not become
trusted publication evidence. Main native jobs remain isolated; only mutable
publication needs serialization. Cache publication consumes qualified produced
artifacts rather than requesting another proof build. See [cache policy](CACHING.md).

## Mathematical adoption boundary

Ordinary code finalization and cache publication report their actual scoped build
and check coverage. They do not request extra kernel replay or establish a
mathematical interpretation, correspondence theorem or premise validity.
[Incremental kernel replay at substantive adoption](DEVELOPMENT.md#kernel-replay-at-mathematical-adoption)
retains its separate explicit consumer, accepted target and compatible evidence.
