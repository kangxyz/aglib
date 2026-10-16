# Arbitrary pullback on bounded-above derived module sheaves

[ResolvedPullback](ResolvedPullback.lean) constructs
`Scheme.Modules.resolvedPullbackFunctor` from actual term-bounded complexes.
It passes the original underlying presheaf through the projective model functor
in the homotopy category, exact sheafification and geometric pullback, then
Mathlib's native derived localization. The comparison isomorphism, object
formula and map formula retain the actual pulled-back flat models and maps.
The functor is additive, inverts the original sheaf quasi-isomorphisms and
lands in the actual `DerivedCategory.Minus` full subcategory. On termwise flat
inputs, the augmentation gives the displayed comparison with ordinary
termwise pullback. The scheme morphism is arbitrary.

[Pullback](Pullback.lean) descends this construction through the proved
[bounded-complex localization](../../../../Algebra/Homology/DerivedCategory/Minus/README.md).
`derivedPullbackMinus` is a functor between Mathlib's existing bounded-above
derived categories. Its localization factorization, flat-model formula,
comparison on flat inputs and natural identity isomorphism remain public.
The source and target derived-category universes are independent.

[PullbackComposition](PullbackComposition.lean) uses the actual ordinary
geometric pullback composition isomorphism and the original flat-model
augmentation. The second replacement remains a quasi-isomorphism under
pullback because the first pulled-back model is termwise flat. Its natural
comparison gives `derivedPullbackMinusCompIso`, with independent derived
universes for all three schemes. This leaf supplies the comparison itself;
it adds no pentagon, triangulatedness or perfectness-preservation theorem.

The schemes have no Noetherian or affine hypothesis, the coefficient sheaves
have no quasicoherence hypothesis, and the scheme map need not be flat.
Bounds, quasi-isomorphisms, actual chain homotopies and the
explicit `HasDerivedCategory` choices are preserved by the interfaces.
