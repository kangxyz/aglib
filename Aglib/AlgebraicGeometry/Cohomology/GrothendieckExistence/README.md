# Coherent Grothendieck existence

[Proper](Proper.lean) proves coherent Grothendieck existence for every actual
proper `f : X ⟶ Spec (CommRingCat.of A)`, where `A : Type u` is a commutative
Noetherian ring, `I : Ideal A`, `[IsAdicComplete I A]`, and `X : Scheme.{u}`.
It derives local Noetherianity of `X` and constructs
`properCompletionEquivalence I f` between `X.CoherentSheaf` and
`AdicSystem X (idealThickeningIdealSheaf f I)`. Its forward functor is literally
`completionFunctor`, by `properCompletionEquivalence_functor` and `rfl`.
There is no local-ring, flatness, projective-embedding, excellence, dimension,
or realization premise. The focused [proper existence guide](Proper.md) gives
the full endpoint, reconstruction hypotheses, and proof route.

[FullFaithful](FullFaithful.lean) supplies
`completionFunctorFullyFaithful I f` and `properCompletionFullyFaithful I f`
under the same complete-base and properness hypotheses, with the derived
local Noetherian instance for the lower interface.
`properCompletionEssSurj` and `proper_completion_essImage` in
[Proper](Proper.lean) supply essential surjectivity for the original native
adic systems; `properCompletionIsEquivalence` combines the two parts.
The [adic-system category](../../Modules/Coherent/AdicSystem/README.md) retains
the original quotient projections, adjunction units, and transition maps.

[Projective](Projective.lean) is the embedded projective specialization and a
supplier for the proper proof. Given an actual closed immersion
`i : X ⟶ ProjectiveSpace A (ULift (Fin (n + 1)))`, it derives local
Noetherianity and properness of the original composite with `toSpec`.
Its declarations in `AlgebraicGeometry.Scheme.Cohomology` are
`projective_completion_essImage`, `projectiveCompletionIsEquivalence`,
`projectiveCompletionEquivalence`, and
`projectiveCompletionEquivalence_functor`. They use the original base ideal
and completion functor, with no auxiliary realization, vanishing, presentation,
flatness, or local-ring hypothesis.

## Projective construction

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

## Proper descent and algebraization

[ChowSourceEffectivity](ChowSourceEffectivity.lean) applies projective existence
to the same actual Chow modification. The original formal pullback and its
coherent realization feed
[FormalModificationBoundedComparison](FormalModificationBoundedComparison.lean),
which constructs the global formal map and one uniform exceptional-ideal
bound. [Ideal-sheaf induction](../../IdealSheaf/Noetherian.lean) retains
nilpotent structure, and
[ClosedImmersionReduction/IdealInduction](ClosedImmersionReduction/IdealInduction.lean)
supplies effectivity on the original exceptional-power thickenings.
[TwoIdeal/Effectivity](TwoIdeal/Effectivity.lean) combines this effectivity with
the bounded comparison to recover the original base-ideal formal system.

[BoundedCoherentReconstruction](BoundedCoherentReconstruction.lean) separately
constructs coherent realizations of `K`-adic systems from formal comparisons
whose defects are killed by a power of that same `K`, on quasi-compact locally
Noetherian schemes. A bound by an independent ideal uses the two-ideal theorem
and its closed-thickening-effectivity hypothesis; the
[proper guide](Proper.md#same-ideal-reconstruction-and-two-ideal-effectivity)
records the distinction and the resulting bounds.

[Algebraization/Operations](Algebraization/Operations.lean) lifts native
commutative algebra operations to the coherent realization and preserves the
whole family of original quotient maps. Its `properAdicAlgebraization` is
consumed by the
[finite-etale complete-local comparison](../../Morphisms/FiniteEtale/ProperCompleteLocal.md).
The [ordinary cohomology family](../README.md) owns cohomology objects and
formal functions; general scheme and module descent retains the existing
[Descent](../../Descent/README.md) owners.

## Projective generators and finite projective products

[ProjectiveGenerators](ProjectiveGenerators.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ProjectiveGenerators`,
adds two interfaces in `Scheme.Cohomology`. Let `A : Type u` be a commutative
Noetherian ring, `I : Ideal A`, `ι : Type u` a finite coordinate type, and
`e : ι ≃ Fin (n + 1)`. For an arbitrary coherent adic system `F` on
`ProjectiveSpace A ι`, `projective_formal_uniform_h1` supplies a single bound
for H¹ vanishing of all its successive transition kernels after sufficiently
large positive twists. `exists_completion_negativeTwist_epi` constructs a
map to `F` from the completion of one finite sum of negative twists, with
`Epi (p.hom.app (op k))` at every level `k`. No completeness, external graded
realization, or vanishing premise is required. This interface constructs
generators; algebraization of the target uses the effectivity results above.

[FiniteProjectiveProduct](FiniteProjectiveProduct.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FiniteProjectiveProduct`,
proves `Scheme.Cohomology.finiteProjectiveProductCompletionIsEquivalence`.
Its input is a finite `q : Y ⟶ P`, where `P` is the native finite over-product
of projective spaces over `A`, indexed by `Fin n` with finite nonempty
coordinate types `σ i : Type u`. For `[IsAdicComplete I A]`, it gives an
equivalence for the literal functor

```lean
completionFunctor Y (idealThickeningIdealSheaf
  (q ≫ (finiteProductOver (fun i => Over.mk (toSpec A (σ i)))).hom) I)
```

`isLocallyNoetherian_of_finite_projectiveProduct` derives local Noetherianity
of `Y` from the constructed projective embedding. The ideal is pulled back
along the original product structural map. This specializes projective
existence and adds a useful product interface; the proper theorem at the
start of this guide keeps its complete Noetherian-base hypotheses.
