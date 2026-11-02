# Unbounded right-derived functors

This family uses the original cochain complexes, homotopy categories, and
`DerivedCategory` localizations. It does not define another derived carrier or
install a global `HasDerivedCategory` instance.

## Actual Grothendieck endpoint

`Grothendieck` constructs `Functor.unboundedRightDerivedFunctor` for every
additive functor from a Grothendieck abelian category to an abelian category
with a chosen native derived category. The source also uses its supplied
native derived category. Grothendieck size, source and target category sizes,
and the two derived-model universes remain independent.

The definition uses the proved regular-stage K-injective replacement in
`KInjective.Existence.Tower.Replacement` with the native chosen separator.
There is no replacement-existence hypothesis or new class. The original
universal unit is `unboundedRightDerivedFunctorUnit`.

`unboundedRightDerivedFunctorObjIso` computes the functor on any specified
quasi-isomorphism into a K-injective complex. Its unit equation identifies the
comparison with the image of that exact map. The corresponding
`unboundedRightDerivedFunctorReplacementIso` uses the actual constructed
natural augmentation.

`Comparison` specializes the canonical bounded-below comparison and the
exact-left-adjoint derived adjunction to this actual functor. The comparison
identifies both native localization units. The derived adjunction's unit and
counit equations retain the original degreewise adjunction maps. Only the
right adjoint's source category must be Grothendieck for this adjunction.
Importing this leaf also supplies triangulatedness through the generic
instance, without an additivity assumption on the replacement functor.

## Reusable conditional leaves

- `Derivability`: an explicit functorial K-injective replacement and natural
  quasi-isomorphism give the native right derivability structure. Every
  additive functor inverts quasi-isomorphisms between these K-injectives after
  the original localization.
- `Basic`: the native total right-derived functor, universal unit, canonical
  shifts, and supplied-resolution computation equation for those explicit
  inputs.
- `Adjunction`: absoluteness under arbitrary postcomposition, followed by the
  native derived adjunction with the localization of an exact left adjoint.
- `PlusComparison`: the unique bounded-below/full comparison determined by
  the original units, for categories with enough injectives.
- `Triangulated`: descent of the same unit to the homotopy category, then
  triangulatedness using actual replacement arrows and distinguished
  triangles in the right orthogonal to acyclic complexes.

These conditional leaves do not claim replacement existence on their own;
`Grothendieck` supplies that specialization from the actual tower theorem.

## Finite-amplitude computation and coproducts

[Computation/Basic](Computation/Basic.lean) and
[Computation/QuasiIso](Computation/QuasiIso.lean) compare the original
unbounded derived image with the termwise image of an acyclic complex under
the stated finite cohomological-dimension hypothesis. The comparison retains
the original localization unit.

[Coproducts/CoefficientComparison](Coproducts/CoefficientComparison.lean)
retains the original higher-derived maps through an exact coefficient
comparison. [Localization](Coproducts/Localization.lean) and
[Preservation](Coproducts/Preservation.lean) descend coproduct preservation
from the homotopy computation to the same derived functor, with the canonical
comparison and original inclusions. Their finite-amplitude and coefficient
hypotheses remain explicit.

## Boundary and consumers

The current consumer is the unbounded direct-image construction in the
exceptional-direct-image task. No Noetherian, torsion, finite-dimensional, or
base-invertibility hypothesis is used by this generic homological input.

The finite-amplitude interfaces consume a cohomological-dimension bound;
they do not provide geometric bounds. Scheme-specific direct images and
proper exchange belong to the exceptional-direct-image family.

## Additional source entry points

- [ChangeTarget](ChangeTarget.lean)
- [Computation/Basic](Computation/Basic.lean)
- [Computation/QuasiIso](Computation/QuasiIso.lean)
- [Coproducts/CoefficientComparison](Coproducts/CoefficientComparison.lean)
- [Coproducts/Localization](Coproducts/Localization.lean)
- [Coproducts/Preservation](Coproducts/Preservation.lean)
- [ExactAdjunctionComposition](ExactAdjunctionComposition.lean)
- [ExactAdjunctionIdentity](ExactAdjunctionIdentity.lean)
