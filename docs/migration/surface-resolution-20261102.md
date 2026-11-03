# Completed surface-resolution source integration

## Source identity and scope

This integration starts from Aglib main
7545acd876b4ebf73f067d532ffa75263c01e26c and the user-supplied two-part
source snapshot dated 2026-11-02. The local branch also retains main's
58f0a8a22159d4bd7e9bdd03035494b394d95baf CI-lint update; that update changes
no mathematical sources, library operating rules or dependency pins.
The archive identities are:

- surface-resolution-main-20261102-2100-part1-of2.tar.xz:
  SHA25694ca20289a214454f5903ddebf70724f3bdbb28fc0094f02abeb07275799db9b.
- surface-resolution-main-20261102-2100-part2-of2.tar.xz:
  SHA256772f00f73c08f73a39d5d32b1e5df0ec969732f32cd1fb90e0fea5fd807beb0c.

The snapshot shares the main baseline. Its package source hashes were checked
before selecting the completed dependency closure. Historical source-bound
passes identify candidates; they do not substitute for native validation of
the reorganized code. Pending-source drafts, diagnostics, incomplete upper
proofs and unrelated CI/tooling changes are not production inputs here.

## Mathematical interfaces

- [Normal-source domination](../../Aglib/AlgebraicGeometry/Surfaces/Birational/NormalizedPointDomination.md)
  constructs a literal normalized point chain dominating a supplied proper
  birational model, with the actual triangle and function-field maps.
- [Prescribed completion descent](../../Aglib/AlgebraicGeometry/Surfaces/Resolution/CompletionDescent.md)
  retains the supplied chain and its length, terminal pullback and both
  projections. [Supported local-chain spreading](../../Aglib/AlgebraicGeometry/Descent/LocalModification/SurfaceChain.md)
  retains the original stalk square and unchanged complement.
- [Completion rationality](../../Aglib/AlgebraicGeometry/Surfaces/RationalSingularities/Completion.md)
  preserves universal original H1 vanishing when the literal completion is
  a normal domain, without algebraizing an arbitrary completed model.
- [The conditional resolving-chain endpoint](../../Aglib/AlgebraicGeometry/Surfaces/Resolution/RationalDoublePoint/NormalizedResolution.md)
  retains its genuine initial full-cone and earlier complete-base inputs.
  Its later cones, marked paths and finite serialization do not discharge
  those initial inputs from arbitrary rational/Gorenstein hypotheses.

The owning guides record the precise Noetherian, Nagata, dimension,
coherence, coefficient, completion and map hypotheses. The full RES and
RES-QE constructions, uniform all-model pure-p H1 bound and remaining global
geometric trace implications are not claimed complete.

## Native mathematical ownership

Generic ring differentials/exterior maps, module coefficient/line operations,
function-field scalars, tensor sections and adjunction laws precede their
geometric specializations. Relative-normalization comparisons live under
Normalization/BaseChange and Normalization/FunctionField; stalk detection
lives under Morphisms/IsIso. Actual local replacement and supported-chain
descent keep Descent/LocalModification as their owner.

The regular-pair and point one-pole consumers use the same existing native
constructors and complete lower laws. Original universes, scalar actions,
coefficient lines, units/counits and canonical maps are retained. Duplicate
conjugate-adjunction proof and an empty compatibility import are removed.
No definitions-only layer represents an unsupplied geometric theorem.

Existing correct public names, proof bodies and compatible compilation
units are retained. The original affine `Sections.lean` and `TildePullback.lean`
providers are restored byte-for-byte to the pre-integration baseline. The two
section-map formulas live in [Sections/Map.lean](../../Aglib/AlgebraicGeometry/Modules/QuasiCoherent/Affine/Sections/Map.lean),
and the added composition API lives in [TildePullback/Composition.lean](../../Aglib/AlgebraicGeometry/Modules/QuasiCoherent/Affine/TildePullback/Composition.lean).
Only their actual consumers need the focused leaves.

## Validation boundary

The earlier integrated source had successful native source-policy, production
build, generated-entry, style and in-package test coverage. That evidence is
historical and does not establish those checks for the current candidate. The
canonical coefficient parent has since been restored to its original source;
Model and Sections are thin imports of it. The parent retains the 39 original
named declarations and three naturality laws without duplicate implementations.
[The import-repair case](../performance/cases/canonical-split-providers/README.md)
records the earlier repair and the subsequent placement correction.

On the earlier integrated source, production declaration lint and the pinned axiom audit had successful
coverage across seven coarse batches: 9357 implementation modules and 130278
declarations, with no remaining findings or unapproved axioms. The 15 generated
import-only entries retain native source, entry-generation and style coverage.
Six successful batches retain their unchanged actual import closures; the
repaired normalization-chart batch was rechecked on the final source. The
[batching case](../performance/cases/coarse-source-preserving-validation/README.md)
records exact inputs, checker predicates, runs and coverage.

The original single-environment checks encountered the host mapping limit and
did not pass. Coarse producer coverage resolves this integration's remaining
checks while preserving the original toolchain and dependency pins. The earlier final
incremental production build, text style and in-package tests also passed.
The source naming, docstring and unused-premise repairs stay within the migrated
cohort and its direct consumers. Kernel replay, separate mathematical clients
and CI workflow edits are outside this integration.

## Invalidation repair

The repair is based on published tip `5901a32b` and compares mathematical inputs
with pre-integration main `1b737dca`. Stable original providers are restored;
additional APIs use focused leaves and precise consumer imports. The original
coefficient parent is the single canonical implementation; its new import paths
reexport it. Unused exposure-only copies of the original trace and resolution
helpers are omitted, while their original proofs and baseline public APIs remain.

The affected reverse import closure is 518 modules: 73 existing and 445 added,
compared with the earlier 3160, including 2729 existing. These are graph counts;
restoring an already published version also requires matching original caches.

Source policy, native entry generation, text style, 61 changed-implementation
terminal builds, seven additional affected library-consumer builds and six
relevant in-package test modules passed. Two coarse lint batches jointly checked
all 511 affected implementation modules and 7800 declarations with no findings.
Both pinned axiom audits passed using only the three approved foundations.
The final 61-root build required zero frontend invocations after compatible
successes were retained. This is scoped incremental validation; no full Aglib
rebuild, kernel replay or separate client check is claimed.

The [placement follow-up](../performance/placement-edits-in-widely-imported-modules.md#surface-resolution-invalidation-follow-up-2026-11-03)
records original-source preservation, graph scope, failed approaches, actual
validation and native cache boundaries. The original mathematical exclusions and
genuine initial RDP hypotheses above remain in force.
