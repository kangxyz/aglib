# Development and checks

Run commands from the package root. [lean-toolchain](../lean-toolchain) pins Lean 4.34.1; [lakefile.toml](../lakefile.toml) pins Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and declares `Aglib` and `AglibTest`. Keep the pinned [lake-manifest.json](../lake-manifest.json). Production imports use Mathlib and precise lower `Aglib` leaves.

## Mathematical trust

Claimed closed results require source correspondence, explicit hypotheses and
foundation inputs, no transitive `sorry`, and axiom dependencies limited to
`propext`, `Classical.choice`, and `Quot.sound`. Custom and native-computation
axioms cannot discharge a proof. Preserve production dependency boundaries and
identify the source, pinned toolchain/dependencies and successful build. Retain
the existing selected-origin transitive axiom audit in ordinary final validation;
reuse compatible unchanged evidence and check changed or uncovered closure.
Source token checks and ordinary lint do not supply transitive axiom coverage.
This is an existing mathematical trust predicate, not kernel replay or an added
acceptance stage. Independent mathematical review and writing acceptance retain
their governing requirements; conditional theorems retain their premises.

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
Kernel replay is an explicitly requested standalone diagnostic only.

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

All normal workflows must use only incremental checks, including authoring, maintenance, documentation, review, merge, integration and publication. Preserve trusted caches, reuse compatible build and check evidence, reconcile combined changes and fill actual coverage gaps. Reconcile exact source/toolchain/configuration identities and obtain matching caches before building genuinely missing or changed required targets and needed affected consumers. Complete coherent mathematical obligations using focused compilation and repair where they advance the proof, with [build_serial.py](../scripts/build_serial.py):

See the exact-leaf command in the [normal task recipe](#normal-task).

Choose a fresh build receipt directory for each invocation; the helper refuses
to overwrite its prior `cached-check.log`.

The helper accepts `--root ROOT`, `--rehash`, optional native Lake `--outputs FILE` mappings and one or more module targets. It first checks whether the requested targets are already cached, then invokes one ordinary Lake build graph for missing work. Lake schedules dependencies with one capped Lean compiler process at a time; `AGLIB_BUILD_THREADS` selects that compiler's internal parallelism. Expected out-of-date diagnostics from the cache probe are saved in `cached-check.log`; configuration, tool and compilation failures still fail the check. [resource_guard.py](../scripts/resource_guard.py) supplies the same owned-group guard for other commands through `--capped-toolchain --receipt FILE -- COMMAND`. [scripts/README.md](../scripts/README.md) owns detailed runtime and helper interfaces.

Routine validation consists of incremental native compilation, native/batch lint,
relevant in-package tests and basic source/no-sorry checks. Retain compatible
successes and check only failed or changed inputs. Compiler-integrated checks
remain enabled. Tooling changes use affected Python fixture tests.

Do not automatically append kernel replay, additional inventory/negative-control
chains or downstream preparation/build/audit. This applies to full scope, merge,
publication and mathematical adoption. Complex multi-stage repeat-acceptance
chains are prohibited. Independent mathematical review, writing acceptance and
status obligations remain separate and unchanged.

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

The installable [lean-incremental-ci package](../ci/README.md) owns plans,
execution records, individual-check progress and the mandatory final coverage
decision. Aglib's adapter supplies its source inventory, predicates and scope.
It chooses an ancestor with completed native validation through
[`ci_baseline.py`](../scripts/ci_baseline.py), rather than the previous push.
Failed or cancelled runs and green source-only runs do not advance this
baseline. Unverified proof changes therefore remain in the next affected plan,
including after a scripts-only repair. The selector rejects the earlier unsafe
incremental workflow and unavailable validation history; it never silently
substitutes the previous push or a full build. A manual comparison may move the
verified baseline earlier, but cannot skip forward over unchecked changes.

The retained committed adapter keeps its source, verified-baseline, implementation,
source-integrity and finalization guards. Baseline admission and provenance are
unchanged. Native commands retain process ownership and resource limits.

The normal local recipe performs basic source checks and affected Python
fixtures, an incremental native library/test build, native builtin/declaration
lint and selected style lint. It does not prepare or validate the separate
client. Existing selected-origin axiom auditing remains required final-validation
coverage; additional inventory and rejection-control chains are not scheduled.
Use the same external `AGLIB_VERIFY_DIR` to retain compatible successes.
`--native-only` and explicit `--phase providers`, `--phase provider-lint` or
`--phase consumers` restrict repairs to the affected groups. No helper return,
commit, merge or publication creates another acceptance cycle.

`bash scripts/check.sh --full --rehash` selects the full library/test scope with
the same basic checks. It does not request extra diagnostics. Standalone
`check_kernel.py`, `check_negative_controls.py` and
`check_compiled_inventory.py` remain callable only for a specifically requested
diagnostic. An explicitly requested `--phase trust` or `--phase client` retains
its existing diagnostic behavior. Client preparation is required only for that
explicit client request, never for routine checks or a root pin update.

## Memory and explicit diagnostics

Native frontends remain serialized under the configured heap, owned-process-group
RSS and concurrency limits. `AGLIB_BUILD_THREADS` selects compiler parallelism;
`AGLIB_LEAN_MEMORY_MB` and `AGLIB_RSS_LIMIT_MB` are MiB limits. Coordinate shared
build outputs and do not run overlapping Lean jobs.

### Kernel replay at mathematical adoption

Mathematical adoption does not trigger replay. The existing kernel checker is
an optional standalone diagnostic only when specifically requested. Its scoped
output does not claim whole-library coverage or discharge mathematical premises
or independent review. Resolve uncertain source, options, environment and artifact
provenance before adopting a result; a cached artifact alone is insufficient.
For an explicitly requested replay, retain compatible evidence and the selected
operational tool revision separately from the mathematical source snapshot.

Managed remote replay retains the admitted `R5_LEAN_REMOTE_PROFILE` wrapper and
its `LEAN_SYSROOT` overlay for import metadata extraction and replay. The checker
independently resolves the source `lean-toolchain` pin through Elan and requires
the reported physical prefix and overlay library to identify that same backend.
Managed evidence binds the backend, wrapper, profile and Elan locator. Changes
to those inputs require compatible fresh scoped evidence. Unmanaged execution
retains its strict executable/prefix identity check and existing closure keys.
Keep the owned phase's wrapper and resource profile set throughout the check;
selecting its physical backend directly would bypass the admitted resource guard.

The checker captures full identities at start/end and guards exact inputs and search-resolution candidates between batches, including ctime to detect changed-and-restored files. Missing dependency source metadata prevents reuse; incomplete compiled metadata or corrupt selected evidence fails closed. Original bases, records, logs and resource profiles remain immutable; current coverage summaries reference the original evidence and distinguish reuse from fresh execution. Older receipts without dependency metadata require a new closure-bound replay. [Replay mechanics](../scripts/README.md#resource-limits-and-explicitly-requested-kernel-replay) describe the evidence layout and configuration normalization.

## Incremental cache and publication

[Native caching](CACHING.md) owns shared toolchain artifacts, cross-checkout and cross-library reuse, public CI cache release assets, and the reusable producer/consumer protocol. Package options retain ordinary `.lake/build` files for existing audits. Mathlib keeps `lake exe cache get`. The checkout caches below additionally preserve incremental partial progress.

The project cache covers the root and downstream build directories. The top-level package `version`, `enableArtifactCache` and `restoreAllArtifacts` in each root/client TOML file are omitted from semantic configuration hashing; these storage-policy flags preserve pre-migration cache keys. All other configuration fields and executable `lakefile.lean` bytes remain significant. The `.aglib-cache.json` wrapper stamp is advisory provenance, not proof of each output's compiler identity. Missing, malformed, schema-mismatched or compiler/toolchain/configuration-mismatched wrapper metadata preserves outputs. Lake's current input/output traces and matching artifact cache select reusable outputs and rebuild only the actual affected closure through `--rehash`; obsolete owned module outputs are pruned. Diagnosed corrupt or untrustworthy native data requires separate scoped fault recovery. Dependencies remain outside those owned roots. See [incremental cache details](../scripts/README.md#incremental-ci-build-cache).

CI uses explicit cache restore and save steps. Newly acquired dependency proof caches are saved after the matching fetch succeeds, before the project check. Project outputs are eligible for saving even when a later check fails, provided restoration supplied a primary key and compiler/cache preparation succeeded. Immutable project-cache generations include the GitHub run ID and attempt, so identical-source retries can preserve further build progress. Restoration tries the same source and configuration first, then the same configuration, then the same OS and architecture. Restored outputs undergo obsolete-module pruning and native Lake `--rehash` trace validation; wrapper stamps do not validate or invalidate all outputs.

Main-branch CI runs serialize without cancelling the active run, allowing eligible build progress to be saved before the next snapshot starts. GitHub keeps the latest pending snapshot in that group. Other branches and pull-request refs cancel superseded active runs. See [workflow concurrency](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/control-workflow-concurrency).

A build-cache hit supplies compiled artifacts, not mathematical acceptance.
Publication reuses compatible routine build/lint/test evidence and fills actual
gaps. It does not trigger replay, downstream checks or repeated certification.
Independent mathematical and writing review retain their existing obligations.

[generate_imports.py](../scripts/generate_imports.py) owns aggregate imports. The generator owner updates enrollment; `python3 scripts/generate_imports.py --check` detects drift. Modern `module` headers, precise `public import` and exposed public sections define the consumer/reduction boundary. [AglibTest](../AglibTest) and [examples/downstream](../examples/downstream) remain consumers, with rejection controls outside production imports.

Lean's default `maxHeartbeats` is 200000, and Mathlib uses that default. An override of any option with an exact `maxHeartbeats` name component, including `synthInstance.maxHeartbeats`, must use a positive finite budget in a declaration-local scope (`set_option ... in`), with a comment after `in` explaining why it is needed. The pinned [style linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Style.lean#L78) requires local scope, and the [heartbeat-comment linter](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean#L103) requires the explanation. Aglib additionally forbids `0`, which means unlimited, even with a valid local explanation; this numeric restriction is stricter than pinned Mathlib. Measure a declaration with `#count_heartbeats in` and leave headroom; Mathlib's [counting guide](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Util/CountHeartbeats.lean) suggests a sufficient budget of the form `2^k * 200000`.

## Contribution conventions

Keep maintained text, identifiers, comments and documentation in English. Follow Mathlib source style and the [naming conventions](NAMING.md). Use the pinned Lean and Mathlib versions; dependency changes require their own coordinated update.

Current source author headers credit `kangxyz`. Credit actual contributors when they contribute; do not enforce a permanent single-author list or add blanket tool attribution. Preserve copyright and Apache 2.0 license notices. Keep historical source identities and correspondence in [REFERENCES.md](REFERENCES.md) and the existing migration records; current author credit does not erase provenance.

Update the owning family README when an object, namespace, hypothesis, result or canonical map changes. Keep cross-family architecture, development and provenance in `docs/`. New families need an admitted object or result and a current consumer, rather than empty scaffolding.

Preserve foreign changes and exact write ownership. Inspect `HEAD` and worktree status before writing and before staging or committing; coordinate overlapping edits and shared build outputs. Keep Git index and `HEAD` mutations serial. Do not push without an explicit current request.

Use incremental build, native/batch lint and relevant in-package tests during
development, integration and publication, preserving basic source correctness.
These execution checks do not discharge mathematical premises or independent
mathematical and writing review obligations.

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
