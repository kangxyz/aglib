# Incremental CI contract

The reusable [lean-incremental-ci package](../ci/README.md) owns execution,
individual-check progress and final acceptance. [Aglib's adapter](../scripts/ci_pipeline.py)
owns its mathematical source inventory, check predicates, affected scope and
historical coverage policy. The workflow owns prepared toolchains, cache
transport and publication authority. A skipped workflow step cannot waive a
required core phase or task.

## Committed source and verified coverage

CI validates the current committed source. The core binds HEAD, every tracked
source/configuration file and the actual executing package implementation. This
also applies to an installed package outside the repository: its code content is
part of the plan and check identity. Aglib additionally requires those bytes to
match its committed package owners. Temporal observations detect mutation and
restoration during execution; installation paths and timestamps are not content
compatibility keys.

A baseline is an ancestor with identifiable successful native validation in an
exact GitHub run attempt. Source-only green runs, failed attempts and the former
previous-push protocol cannot establish that baseline. The adapter explicitly
admits reviewed workflow and recipe identities; it does not infer execution from
shell commands found inside YAML. The historical legacy witness is restricted
to source commit `cc17eecf0344f15c89ffc04cade60b1b09cf9f43`, its exact workflow
and its exact whole-native recipe. Core recipes bind actual package and adapter
implementation owners. Unknown or unavailable evidence fails with a recovery
diagnostic, without choosing an empty scope or an implicit whole-library build.

Manual bases may widen a verified range. They cannot advance over unverified
changes. A source-only run may inherit coverage only when mathematical inputs,
semantic check policy and required controls are compatible with its verified
ancestor. A change to CI execution machinery requires native integration even
when the Lean source is unchanged.

The core reconstructs required tasks from the committed adapter. Completion
requires the exact source-bound task set, successful resource receipts and
compatible individual-check records. Incomplete, skipped, corrupt, stale or
wrong-invocation records do not supply acceptance. Finalization precedes native
artifact publication.

## Compilation and upstream changes

Lake owns compilation dependency and artifact identity. The adapter uses one
shared `lake --rehash` build of the current library/test graph and required
checker imports, then a final `--no-build` graph barrier. Git differences select
additional checks; they do not certify compiled artifacts or replace Lake's
hashes. Unrelated cold imports in an ordinary affected scope are a diagnosed
cache recovery gap, not an invitation to compile an unrelated forest.

Dependency, compiler or build-configuration transitions assign complete current
check coverage explicitly. This is a validation scope, not a force-rebuild:
matching artifacts for the new inputs remain usable. The workflow first restores
prepared dependency/project/native caches and obtains matching Mathlib cache;
Lake then decides which targets need compilation. A missing matching artifact
can require compilation, but a version label alone does not establish the
number of necessary builds. See [upgrade/cache semantics](CACHING.md#upstream-and-toolchain-updates).

Production declaration lint uses the unchanged Batteries driver on the complete
`Aglib` umbrella environment. It runs as one guarded command, rather than once
per production leaf. Test declaration lint likewise runs once on the complete
`AglibTest` umbrella environment, and selected `AuditSupport` is checked separately.
These environment predicates are explicit in
the plan and summary; no equivalence to per-leaf lint is asserted, and old
exact-origin successes are not re-keyed as umbrella successes.

Builtin lint runs once for each production/test root, text style runs once for
its selected sources, and the fixed axiom auditor
checks the `Aglib`/`AglibTest` origin prefixes in one invocation. Extra tool
origins remain explicitly selected. Builtin, declaration and audit commands use
separate guarded processes, releasing one environment before the next. No extra input
ledger or cross-version check-compatibility protocol is required.

Aglib tracks its deterministic downstream manifest. Regenerate it with
`python3 scripts/prepare_downstream.py` and commit it with a root pin update.
Planning rejects stale tracked client metadata before expensive native work.
Preparation preserves identical bytes and establishes ignored cache links before
optional-input observations begin.

Native frontends remain serialized under the configured heap, owned-process-group
RSS and concurrency bounds. An explicitly admitted parent-managed resource
profile retains its actual wrapper and physical runtime identities. Unsupported
custom compiler identity overrides are rejected. The package does not promise
arbitrary cross-version import compatibility.
Each native task's working directory must resolve the root's same compiler and
physical runtime; a distinct downstream toolchain is rejected before execution
or reuse. Update coordinated root/client pins together.
The prepared toolchain installation and Elan selection configuration remain
immutable during the attempt; compiler-file guards do not monitor arbitrary
external Elan override changes between launcher lookups.

## Independent check progress

A native trace certifies neither declaration/builtin lint nor an axiom audit.
Per-check success binds the selection, current native outputs, checker and
runtime implementation, source/policy data, actual compiler/shared libraries,
arguments and declared environment. Reflective checks follow all explicit
imports from supported `.ilean` metadata, including private/meta branches, and
bind the relevant artifact families. Search resolution follows pinned Lean's
namespace-root behavior, actual ordered paths, implicit `Init` and workspace
shadows. Unsupported metadata disables check reuse and selects actual execution.
Custom setup import overrides remain outside this metadata guarantee.

Hashing and import discovery are shared within a phase. Each check retains its
relevant closure. Optional policy files and preceding resolution candidates
include temporal absence observations; a file or shadow appearing and then
being removed cannot supply a compatible success. Compiler/runtime inputs are
observed before each success can be saved, including reflection-disabled paths.

Only completed commands with exit zero, no guard failure and a closed owned
process group create successes. A later failure retains those valid individual
successes and compatible compiled artifacts. It does not create complete CI
coverage. Relocated identical checkouts can reuse compatible content records;
original execution paths remain receipt provenance. Cheap source/style checks
may execute again rather than use an insufficiently bounded cache rule.

## Initial policy cutover

The first core rollout explicitly retains the actual legacy policy for unchanged,
baseline-enrolled origins whose relevant local import closure and pins remain
unchanged. This admission is restricted to the exact reviewed source/recipe and
adapter transition. It is not a conversion of old receipts into new check keys.

The legacy recipe declaration-linted production origins in the `Aglib` umbrella
environment. It supplied no independent Batteries declaration coverage for
`AglibTest` or `AuditSupport`. Legacy test build/builtin/style/trust coverage is
reported separately. Style membership comes from the baseline root imports;
the root source files themselves are not silently added to that old enumeration.
New, changed and affected origins receive the current selected checks. The
summary reports the retained policy, witness and origin-inventory digest, and
does not claim per-leaf equivalence with the old umbrella environment.

An unbounded semantic checker/policy change cannot inherit older predicates.
It needs assigned current category coverage or an explicitly validated migration;
configuration transitions execute complete current categories. Mathematical
source equality alone is insufficient.

## Fixed Lean audit and fixture sources

The selected-origin auditor is the committed
[SelectedAudit.lean](../ci/lean/SelectedAudit.lean) program. The shared
[Python adapter](../scripts/ci_audit.py) passes one JSON argument containing
arrays of module-name components. It validates the identifier grammar and
rejects empty selections, path aliases, separators and control characters.
Selection is decoded as names, never parsed or evaluated as Lean source.

The fixed program builds the same legacy import sequence in a fresh private
environment and preserves the source frontend's actual options and trust level.
Its own helper declarations and additional API imports do not enter the audited
environment. The existing origin, root-namespace, private and generated-declaration
controls remain enabled, and logged errors fail the invocation. Unsupported
syntax-valued frontend options fail closed.
The migration covers the adapter's fixed audit invocation and its audit
predicates. It is not a replacement for arbitrary frontend deprecation,
portability or `--error=kind` diagnostic modes.

The helper and driver hashes are pinned through the existing CI adapter recipe
owner and included in check inputs. Their first introduction has an explicit
reviewed migration from the exact prior generator and the exact prior audit
support, coverage and control sources; later semantic changes cannot
inherit this exception. The real cache test copies fixed
[Quartz fixture sources](../ci/fixtures/quartz) into its isolated producer and
consumer trees, verifying their reviewed content hashes before use. Temporary
working directories contain copies and build outputs; the maintained Lean source
is directly reviewable in Git.

## Cache trust, tests and result

Native/build/check caches retain a reviewed trusted-producer boundary. Native
Lake hashes describe build identity; they are not adversarial provenance proofs.
Partial cache availability does not mean CI passed. The workflow saves partial
progress after failures and publishes accepted coverage only after finalization.
This follows Mathlib's separation of build progress, lint/test gates and cache
publication, while retaining Aglib's own stricter finalizer policy. See its
[native build and no-build barrier](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/scripts/lake-build-with-retry.sh#L27-L52),
[partial-cache staging](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml#L285-L340)
and [native-cache producer/consumer integration](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/lake_cache_shadow.yml#L551-L606).

Package unit tests use a separate library/protocol. The bounded real
[cache integration](../ci/native_test.py) uses two copies of a two-module Lean
package and isolated local caches. It checks retained success after a later
failure, matching restoration under `--no-build`, rejection of stale upstream
inputs and restoration for the new inputs. It runs for core/toolchain changes;
it does not rebuild Aglib or update its pins. Its same-compiler results are not
a cross-version compatibility claim.

Complete output distinguishes performed checks, reused individual successes,
inherited policy and compiled-or-refreshed trace diagnostics. The latter are not
an actual compiler-invocation count. Ordinary code validation does not claim
additional kernel replay or mathematical adoption; those remain governed by
[formalization acceptance](DEVELOPMENT.md#kernel-replay-at-mathematical-adoption).
