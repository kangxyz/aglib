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
units are retained. The two affine section-map formulas stay in the existing
section-functor property provider; adding another module during validation
would invalidate an already compiled long dependency chain. Topic
enrollment is limited to affected families.

## Validation boundary

The native source-policy check, complete production-library build,
generated-entry check, text style and in-package tests have passed on the
reorganized source. The coefficient entry reuses the canonical Model and
Sections providers and retains its three original naturality proofs;
[the import-repair case](../performance/cases/canonical-split-providers/README.md)
records the source correspondence and successful production build.

Production declaration lint and the pinned axiom audit now have successful
coverage across seven coarse batches: 9357 implementation modules and 130278
declarations, with no remaining findings or unapproved axioms. The 15 generated
import-only entries retain native source, entry-generation and style coverage.
Six successful batches retain their unchanged actual import closures; the
repaired normalization-chart batch was rechecked on the final source. The
[batching case](../performance/cases/coarse-source-preserving-validation/README.md)
records exact inputs, checker predicates, runs and coverage.

The original single-environment checks encountered the host mapping limit and
did not pass. Coarse producer coverage resolves this integration's remaining
checks while preserving the original toolchain and dependency pins. The final
incremental production build, text style and in-package tests also passed.
The source naming, docstring and unused-premise repairs stay within the migrated
cohort and its direct consumers. Kernel replay, separate mathematical clients
and CI workflow edits are outside this integration.
