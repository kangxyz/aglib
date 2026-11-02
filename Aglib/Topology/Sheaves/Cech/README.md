# Cech constructions on topological opens

These constructions use the actual opens of a topological space and the original
Cech complex. The presheaf-level restriction and cocycle leaves retain the native
`CategoryTheory.Cech` namespace. The additive sheaf comparison lives in
`TopCat.Sheaf.Cech`; its section-cycle normalization lives in
`TopCat.Sheaf.Cohomology`.

[Restriction](Restriction.lean), imported as
`Aglib.Topology.Sheaves.Cech.Restriction`, contains `intersectFunctor`,
`intersectToId` and `restrictPresheaf` for the original intersection restriction.
`intersectToIic` and `iicInclusion` retain the opens-below adjunction.
`restrictedCech_exactAt_succ` proves positive-degree exactness after restriction
to a selected member, with abelian coefficients and the stated product
universes. `cechCosimplicialIntersectIso` identifies the actual cosimplicial
objects when every family member lies in the fixed open; it retains arbitrary
coefficient categories with the required products.

[Cocycles](Cocycles.lean), imported as
`Aglib.Topology.Sheaves.Cech.Cocycles`, uses a module-valued presheaf on actual
opens. `tupleOpen`, `sectionRes` and `cochainVector` retain the literal finite
intersections, restrictions and product-coordinate maps. The differential
formula and `cechOne_vector_closed` use the original Cech complex.
`cechOne_coboundary_of_exact` and `exists_cechOne_coboundary_of_exact` turn the
stated degree-one exactness and cocycle equations into actual sectionwise
coboundaries. The original space/ring/index universe context is unchanged;
these results do not supply that degree-one exactness premise.

The restriction and cocycle source split retains the existing implementations
from revision `451aeda6b8bb5b44402b574dd6cf60f912360f8c`, with their declarations,
conditions, maps and proofs.

The sheaf comparison follows this pipeline, with ordinary focused imports:

- [SectionCycles](../Cohomology/SectionCycles.lean), imported as
  `Aglib.Topology.Sheaves.Cohomology.SectionCycles`, constructs
  `resolutionSectionClass` and `resolutionSectionsCohomologyEquiv` for a supplied
  additive injective resolution. The original section cycles modulo boundaries
  compute positive `Sheaf.H`; `resolutionSectionClass_naturality` retains the actual
  coefficient map and supplied resolution lift.
- [Resolution](Resolution.lean), imported as
  `Aglib.Topology.Sheaves.Cech.Resolution`, supplies native open-free section
  representability, `sheafHPrimeTopAddEquiv` with its constant-integer and
  degree-zero section normalization, `additiveResolutionHomologyEquiv`, and
  `additiveInjectiveCech_exact_succ`. Its stalk-skyscraper argument is for
  topological spaces; positive row exactness needs no covering premise.
- [Comparison](Comparison.lean), imported as
  `Aglib.Topology.Sheaves.Cech.Comparison`, constructs
  `additiveCechResolution`, its row and column augmentations, and their maps into
  the same first-quadrant total complex. `HasExactIntersections U R` states
  positive exactness of the actual resolution-section complexes on all finite
  tuple intersections. Together with `iSup U = ⊤`, it gives
  `additiveCechResolutionHomologyIso` in every degree and
  `additiveCechCohomologyAddEquiv` in positive degrees.

Alongside this pipeline, [Augmentation](Augmentation.lean), imported as
`Aglib.Topology.Sheaves.Cech.Augmentation`, defines `cechAugmentationZero`,
its component and signed-differential equations, and the natural cochain map
`cechAugmentation`. These constructions use a presheaf with preadditive
coefficients admitting the required products (and a zero object for the cochain
map); they need neither a sheaf condition nor a covering premise.

For additive sheaves, `HasAcyclicIntersections U A` states vanishing of the
original positive `Sheaf.H'` on every finite tuple intersection.
`HasAcyclicIntersections.exact` supplies the section-exactness hypothesis for
any additive injective resolution. The canonical positive-degree API is
`cechCohomologyAddEquiv U hcover A hA n`, with target `Sheaf.H A (n + 1)`;
it chooses one injective resolution internally.
`cechCohomologyAddEquiv_naturality` uses the original coefficient map without a
supplied lift. The supplied-resolution API remains available, with
`additiveCechCohomologyAddEquiv_independent` and
`additiveCechCohomologyAddEquiv_eq_canonical` identifying its values.

All these comparisons retain the original complex, quotient, alternating signs,
augmentations and constant-integer/section normalization. This topological
argument makes no enough-points assertion for arbitrary sites and uses no
`CoverResolution` interchange. The lower
[generic Cech family](../../../CategoryTheory/Sites/SheafCohomology/Cech/README.md)
owns arbitrary-category split exactness, coefficient comparison and generic
module short-exact-sequence calculations. Actual quasicoherence, affine
intersections and separatedness enter through the
[Scheme applications](../../../AlgebraicGeometry/Cohomology/Cech/README.md).
