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

## Boundary and consumers

The current consumer is the unbounded direct-image construction in the
exceptional-direct-image task. No Noetherian, torsion, finite-dimensional, or
base-invertibility hypothesis is used by this generic homological input.

Finite-cohomological-dimension computation on unbounded acyclic complexes,
the geometric direct-image specializations, and unbounded proper base change
remain separate obligations. This family does not by itself close D4's
finite-dimensional computation or the exceptional calculus.
