> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#étale-derived-comparisons-share-the-equation-then-specialize) · [Context](original-context.md) · [Case index](README.md) · [Previous record](site-cohomology-share-the-comparison-definition-not-only-its-proof.md) · [Next record](why-a-short-proof-can-be-expensive.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Étale derived comparisons: share the equation, then specialize

These entries retain the delivering author's reported native build observations
from the adopted source packet, at the stated source versions. The packet
contains source identities and status records; its historical timings are not
measurements made by the present integration run.

The bounded-below étale comparison work on 2026-10-22 supplies two further
examples of the literal-boundary method above. These are native incremental
module results on the pinned dependencies, starting from Aglib `c6f64b5b`;
heartbeat and process caps were not increased. They establish successful
compilation of particular source versions, not controlled speedup ratios,
whole-library acceptance or a compiler defect.

### Exact-square conversion

A concrete proof of `derivedInverseImageSquareIso_exactComparison` in
[Derived/BaseChange](../../Aglib/AlgebraicGeometry/EtaleCohomology/Derived/BaseChange.lean)
failed with `(kernel) deterministic timeout`. The generic exact-square proof
already compiled, but specializing a separately expanded concrete equality
still required an expensive native conversion.

The successful boundary uses `ExactComparisonSquareEquation` in
[ExactSquare](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/ExactSquare.lean):
a definition of the literal original equality, parameterized by the functors,
ordinary square, derived square and complex. The generic
`exactComparisonSquareEquation` proves that formula over abstract functors;
the concrete theorem states the same predicate and supplies the canonical
inverse-image comparisons. Only the named square constructors and equality
transport are normalized at the concrete boundary. The related
[UnitComparison](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/UnitComparison.lean)
uses `DerivedMateUnitEquation` in the same way. These predicates are explicit
equalities with proved witnesses, not replacement assumptions or opaque
certificates.

The repaired exact-square provider, unit-comparison provider and concrete
`Derived/BaseChange` leaf compiled in 2.6, 2.0 and 4.0 seconds, respectively.
The concrete leaf had previously failed after a 62-second task. Since the
baseline failed and the source changed, those times are not a speedup ratio.
The actual square, original units, universes and mathematical hypotheses remain
part of the interface.

### Cocycle elaboration

A concrete cocycle comparison in
[PullbackComposition](../../Aglib/AlgebraicGeometry/EtaleCohomology/PullbackComposition.lean)
instead exhausted the elaborator's `whnf` limit of 200000 heartbeats. This is
not the preceding kernel-timeout diagnostic. The successful refactor moves the
cycle-class map law to `HomologicalComplex.addCommGrpCycleClass_map` and the
Ext/right-derived comparison to
`InjectiveResolution.extRightDerivedAddEquiv_cocycle_natTrans` in
[CocycleComparison](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/CocycleComparison.lean).
Their arguments are abstract complexes, an injective resolution and an additive
natural transformation. The concrete application supplies the original
constant-integer/global-sections transformation instead of repeating its
resolution and homology calculation inside the scheme-specific proof.

The generic leaf compiled in 2.7 seconds. Subsequent normalization repairs and
specialization yielded a successful 169-second `PullbackComposition` compile,
including the equality of the original all-degree cohomology pullback with the
actual canonical derived-global-sections pullback. Generic acceptance alone did
not establish that endpoint; its concrete module had to pass too.

Use small reusable lemmas with explicitly typed arrows and the same literal
formula on both sides of the abstraction boundary. Import their owning leaves,
retain successful dependencies and continue only the affected incremental graph;
a documentation update creates no new compilation or validation obligation.

### Degree-zero specialization: preserve the actual maps as parameters

The concrete degree-zero comparison still hit a native kernel timeout in the
run that accepted `PullbackComposition`. Sharing the conclusion predicate and
then the unit/transport input predicates did not suffice: the next concrete
specialization also timed out, despite acceptance of its generic provider.

The successful boundary in
[ActualZeroComparison](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/ActualZeroComparison.lean)
keeps the actual ordinary, derived and higher exchange maps, comparison
isomorphisms, and source/target transport arrows as typed abstract parameters.
Separately proved canonical equalities identify these parameters with the native
mates, comparison isomorphisms and transport formula. Substitution of those
witnesses occurs only in the abstract proof, not in the large concrete sheaf
calculation. Here “opaque parameters” means abstraction by theorem arguments,
not changing the canonical definitions to Lean `opaque` declarations.

The generic `higherExchangeZero_normalization_actual` and its actual-unit
adapter compiled in a 2.0-second provider task. The concrete leaf next accepted
five canonical alias lemmas: the ordinary mate, native derived adjunction,
derived mate, higher-direct-image comparison, and higher-map transport
identifications. The final `Derived/BaseChange` leaf then compiled in 11 seconds
on 2026-10-23, including `higherBaseChangeMap_zero` for the actual canonical
maps. This last consumer acceptance, rather than the earlier generic or alias
acceptance, establishes the successful degree-zero specialization.

No mathematical assumptions, maps or resource caps were added or changed, and
no separate kernel replay was used. This is a successful compilation boundary,
not a controlled speedup ratio or acceptance of every derived coherence target.
The lesson is stronger than naming a proposition: preserve the actual map and
comparison arguments throughout the concrete application, and move their
canonical substitutions behind the generic boundary as well.


### Native whiskering conventions for higher horizontal pasting

The final 2026-10-23 continuation adds a precise convention to the same method.
For nested coefficient prewhiskering and homology postwhiskering, the generic
supplier must return the consumer's literal `whiskerLeft J (whiskerRight β H)`.
Normalize `Functor.whiskerRight_left`, `whiskerLeft_twice` and
`whiskerRight_twice` over abstract categories while retaining the required
associators. Substituting concrete exchange arrows before this normalization
left the delivering author's higher-horizontal witnesses at a kernel
`deterministic timeout` in runs119 and121.

Even a concrete `congrArg (whiskerLeft P)` factor proof could retain expensive
conversion. `HigherWholePasting.mapped_horizontal_second_native` accepts the
original unwhiskered source-comparison and exchange equations, constructs their
whiskered forms in the abstract helper, and returns the native convention.
`whole_second_reassociate` handles the last comparison-source association.
Assemble the whole transformation before extracting its final component.

The corrected generic provider compiled in delivery run123; run124 then
compiled the raw concrete leaf. Final run125 compiled HigherWholePasting in
2.9 seconds and the complete Derived/BaseChange consumer, including
`higherBaseChangeMap_hComp`, in228 seconds. The two final source hashes are
`513e0413705b92c3950dd8f0151fc63917d0e52a9a9fdee1196ef3386b8b3258`
and `9833e77023b1d94956a783e83d2d89446e842dd864d112d91e19e79ab876ff31`.
These are retained author observations from archive
`etale-coherence-source-20261023T040650Z.tar.gz`, with source and log records;
the failed diagnostics do not state a numerical heartbeat budget. No source
budget override, replay or new benchmark was used, and no speedup ratio or
compiler-defect claim follows from the changed-source observations.

### Higher exchange components: retain the whole transport equation

The original higher-exchange consumer in
[`Proper/Reduction/Composition`](../../Aglib/AlgebraicGeometry/EtaleCohomology/Proper/Reduction/Composition.lean)
encountered a kernel `deterministic timeout` when a concrete `change` exposed
its source isomorphism, mapped original derived mate and target isomorphism
at once. On Lean 4.34.1 and Mathlib `d13f23b7`, run
`remote-976f2775cb4446c5a5bb25b1d9d7739a` failed this Composition leaf
(source `aae7ec921785deb277e91f4571ffadc411beee2762332361fad90c50f7efab6b`);
Lake reported 152 seconds for the module. The standard 200000-heartbeat
budget was retained, and no OOM was observed.

The repair proves `isIso_app_of_whiskered_transport` over variable categories,
functors and original transformations. It accepts the literal whole equation
`δ = s.hom ≫ whiskerLeft J (whiskerRight β H) ≫ t.hom` and invertibility
of the original `β.app (J.obj X)`. Only that typed helper expands the native
whiskering component. The concrete consumer supplies the existing whole
`higherBaseChangeMap_eq_transport` and preserves its original coefficient,
source/target comparisons, derived mate and four derived-category universes.
It needs no concrete component conversion or new premise.

The repaired source
`1b0b3c0166c0ade282a78d7ac80bc78029920e179f96f26f5374f524eeab856d`
compiled in 5.5 reported module seconds in
`remote-e3f48a4100624625bb4632ca1f4d0ce0` with the unchanged standard budget.
That batch accepted Composition and Retracts but failed a separate record-layout
error in InjectiveRetract; it was not a successful three-leaf run. These are
source-bound incremental observations, not a controlled speedup benchmark,
compiler-defect claim, new profile or kernel replay.

### Finite Ext tests: isolate witness selection

In
[`Ext/BiproductComparison`](../../Aglib/Algebra/Homology/DerivedCategory/Ext/BiproductComparison.lean),
the actual `Ext.addEquivBiproduct` source and target equivalences were already
typed at their original coefficient carriers. Selecting componentwise
preimages inside the specialized surjectivity proof still exhausted the
standard 200000 heartbeats at `whnf`. This occurred in
`remote-8c4ef9011fcb408e8cb017d79e1d1137`, source snapshot
`4ec8c76c3be06c267eba21d07018946fabe806ddeb4ab4d467c468df33c99b35`;
the subsequent unknown-constant error was cascading.

The validated repair puts witness selection and inversion of the product
equivalences in private `surjective_of_pi_transport`, parameterized by plain
functions, two actual equivalences and their literal component equation.
The Ext consumer supplies its original comparison, native additive
equivalences and original coefficient-naturality equation. The public
statement retains arbitrary finite-index universes, independent Ext sizes,
a preadditive source and an additive coefficient functor; no premise or
budget is added.

The exact repaired leaf
`8851e330dd2ae53f1b26f3876078379849302c51a5f3e9d12eb3a6697229fb77`
compiled without diagnostics in
`remote-1aca77219a7c4e619c3b814d976be5be`, whose source manifest
`6b15739f5f2dc67137f8e663a118c2b0904f8cd1a47f96768f1d2a127a9fdd1d`
contains that leaf hash. Its one frontend succeeded; recorded wall time was 7.7 seconds. These are changed-source compilation
observations, not a controlled benchmark, new diagnostic run or kernel replay.

