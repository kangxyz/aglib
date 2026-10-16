# Bounded-above cochain complexes

[Basic](Basic.lean) uses the existing `HomologicalComplex.IsStrictlyLE` predicate
to define `CochainComplex.boundedAbove` and its full subcategory
`CochainComplex.BoundedAboveComplex`. Its morphisms are the original chain maps.
`chosenUpperBound` selects a bound and `chosenUpperBound_spec` retains the actual
termwise vanishing. The ambient category is arbitrary abelian, with independent
object and morphism universes. The same leaf defines `boundedAboveQMinus` into
Mathlib's existing `DerivedCategory.Minus`, proves essential surjectivity using
strictly bounded representatives and proves that original quasi-isomorphisms
become isomorphisms. The derived-category universe remains an explicit choice.

[ProjectiveReplacement](ProjectiveReplacement.lean) assumes enough projectives
and constructs a termwise projective complex and an actual quasi-isomorphism
to the original complex, with exactly the supplied strict upper bound. Its
lower [opposite quasi-isomorphism rules](../OppositeQuasiIso.lean) concern
unbounded complexes and retain the actual integer-negation and opposite maps.

[ProjectiveHomotopy](ProjectiveHomotopy.lean) chooses these models and original
augmentation maps. It constructs comparison chain maps and actual comparison
homotopies. Identity, composition and addition hold after passing to the
homotopy category, giving an additive functor and a natural augmentation there.
The source covers are not asserted to be additive functors of chain complexes.
The lower [K-projective comparisons](../../DerivedCategory/KProjective/README.md)
work without a term bound.

[Native D− localization](../../DerivedCategory/Minus/README.md) identifies the
quasi-isomorphism localization of these actual bounded complexes with the
existing ambient bounded-above derived category. The full category of
term-bounded complexes and the cohomologically bounded derived category remain
distinct objects connected by that localization functor.
