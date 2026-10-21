# Coherent Grothendieck existence

[Projective](Projective.lean) proves coherent Grothendieck existence for an
actual closed immersion
`i : X ⟶ ProjectiveSpace A (ULift (Fin (n + 1)))`. The base `A` is an arbitrary
commutative Noetherian ring, `I : Ideal A`, and `[IsAdicComplete I A]` supplies
completeness. Local Noetherianity of `X` and properness of the composite
`i ≫ toSpec A (ULift (Fin (n + 1)))` follow from the embedding.

The public declarations in `AlgebraicGeometry.Scheme.Cohomology` are:

- `projective_completion_essImage`: every native coherent adic system lies in
  the essential image of its original completion functor.
- `projectiveCompletionIsEquivalence`: that completion functor is an equivalence.
- `projectiveCompletionEquivalence`: the equivalence of `X.CoherentSheaf` with
  `AdicSystem X (idealThickeningIdealSheaf (i ≫ toSpec A _) I)`.
- `projectiveCompletionEquivalence_functor`: its forward functor is literally
  `completionFunctor`, by reflexivity.

These statements have no auxiliary realization, vanishing, presentation,
flatness, or local-ring hypothesis. The formal objects and morphisms belong to
[the native coherent adic-system category](../../Modules/Coherent/AdicSystem/README.md).
The quotient projections, adjunction units, and transition maps are retained.

[FullFaithful](FullFaithful.lean) also supplies
`properCompletionFullyFaithful I f` for any proper
`f : X ⟶ Spec (CommRingCat.of A)` over the same complete Noetherian base.
Local Noetherianity is derived from properness. This theorem proves full
faithfulness; essential surjectivity for general proper schemes remains open
in this family. The equivalence endpoint here requires the actual projective
embedding above.

## Proof organization

[Completion](Completion.lean), [CompletionNaturality](CompletionNaturality.lean),
and [CompletionFunctorComparison](CompletionFunctorComparison.lean) compare the
native ideal-sheaf completion with the original base-ideal quotient tower.
The `FullFaithful*` and completed-section modules recover coherent morphisms
through coherent internal Hom and degree-zero formal functions.

The `Graded*` modules construct the associated-graded action directly from the
successive kernels of the given formal system. Affine tensor charts, their
original restrictions, and finite generation produce coherent realizations.
[GradedRealization](GradedRealization.lean) and
[GradedRelationRealization](GradedRelationRealization.lean) supply the formal
coefficient and ordinary relation realizations used by the projective proof.
The relation kernels are taken in the ambient diagram category.

[RealizationVanishing](RealizationVanishing.lean) derives the uniform Serre bound.
[ProjectivePresentation](ProjectivePresentation.lean) and
[RelationPresentation](RelationPresentation.lean) construct compatible
presentations by completions of finite sums of negative twists.
[PresentationAlgebraization](PresentationAlgebraization.lean) algebraizes their
cokernel using proper full faithfulness and ambient pointwise right exactness.

[ProjectiveEffectivityOfRealization](ProjectiveEffectivityOfRealization.lean)
records the assembly theorem with explicit realization premises.
[ProjectiveSpaceEffectivity](ProjectiveSpaceEffectivity.lean) discharges those
premises and proves the projective-space equivalence.
[ClosedImmersionReduction](ClosedImmersionReduction.lean) descends effectivity
along the original closed immersion, completing the projective endpoint.
