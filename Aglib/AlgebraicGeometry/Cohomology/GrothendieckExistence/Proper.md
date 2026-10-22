# Coherent Grothendieck existence for a proper morphism

Import `Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Proper`.
The declarations belong to `AlgebraicGeometry.Scheme.Cohomology`.

Let `A : Type u` be a commutative Noetherian ring, let `I : Ideal A`, and assume
`[IsAdicComplete I A]`. For any scheme `X : Scheme.{u}` and actual proper map
`f : X ⟶ Spec (CommRingCat.of A)`, [Proper](Proper.lean) constructs

```lean
properCompletionEquivalence I f :
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  X.CoherentSheaf ≌ AdicSystem X (idealThickeningIdealSheaf f I)
```

Here `AdicSystem` and `completionFunctor` belong to
`Scheme.Modules.Coherent`. Local Noetherianity of `X` is derived from `f`.
The base need not be local, and no flatness, projective embedding, excellence,
dimension bound, or supplied realization is required.

The equivalence uses the ideal sheaf induced by the original base ideal and
structural map. `properCompletionEquivalence_functor` states, by `rfl`,

```lean
(properCompletionEquivalence I f).functor =
  completionFunctor X (idealThickeningIdealSheaf f I)
```

The native [adic-system category](../../Modules/Coherent/AdicSystem/README.md)
retains the actual module-sheaf diagram, its quotient units, and its transition
maps. The term at index `n` is coherent and killed by the `n`th ideal-sheaf
power. Index zero is zero; index one is the original first thickening. The
completion functor is defined independently of an effectivity theorem.

| Declaration in [Proper](Proper.lean) | Interface |
| --- | --- |
| `properCompletionEssSurj I f` | Essential surjectivity of the original completion functor |
| `proper_completion_essImage I f F` | Every native adic system `F` lies in that essential image |
| `properCompletionIsEquivalence I f` | The original completion functor is an equivalence |
| `properCompletionEquivalence I f` | The coherent/adic-system equivalence |
| `properCompletionEquivalence_functor I f` | Literal equality of its forward functor with completion |

[FullFaithful](FullFaithful.lean) supplies
`completionFunctorFullyFaithful I f` and `properCompletionFullyFaithful I f`
under the same base and properness hypotheses. The lower interface uses the
local Noetherian instance; `properCompletionFullyFaithful` derives it from `f`.
The essential-surjectivity construction supplies the remaining part of the
equivalence.

## Proof route

[Ideal-sheaf Noetherian induction](../../IdealSheaf/Noetherian.lean) applies
to the original quasi-coherent ideals, including nilpotent structure. For a
nonempty closed subscheme, [ChowSourceEffectivity](ChowSourceEffectivity.lean)
uses the [projective Chow modification](../../Morphisms/Proper/Chow/Projective.lean)
and [projective existence](Projective.lean) to realize the given formal
pullback on that same modification. The proper modification is an isomorphism
on a dense open; neither its source nor the closed subscheme is replaced by
its reduction.

[FormalModificationBoundedComparison](FormalModificationBoundedComparison.lean)
constructs a map from the original formal system to the completion of a
coherent proper direct image. Affine formal functions, the original
pullback/direct-image adjunction, and module-Hom gluing retain the actual
map. Affine bounds and a finite open subcover produce one positive power of
the exceptional ideal annihilating all stagewise kernel and cokernel defects.
The exceptional ideal is independent of the base ideal defining completion.

[ClosedImmersionReduction/IdealInduction](ClosedImmersionReduction/IdealInduction.lean)
uses the strict-ideal induction hypothesis to supply effectivity on every
actual exceptional-power thickening. Positive powers use the native
kernel-image factorization; exponent zero is the empty scheme.
[TwoIdeal/Effectivity](TwoIdeal/Effectivity.lean) then descends the realized
system using that closed-thickening effectivity and the bounded formal map.
The empty case is handled by [Empty](Empty.lean). Proper full faithfulness
combines with this essential surjectivity in [Proper](Proper.lean).

## Same-ideal reconstruction and two-ideal effectivity

[BoundedCoherentReconstruction](BoundedCoherentReconstruction.lean) has its
own reusable, more specific interface. On a quasi-compact locally Noetherian
scheme, let `K` be an ideal-sheaf datum, `F : AdicSystem X K`, and
`H : X.CoherentSheaf`. Given
`α : F ⟶ (completionFunctor X K).obj H` and
`AdicSystem.DefectsKilled K t α` (both ordinary component defects are killed
by `K ^ t` at every stage), `exists_boundedCoherentReconstruction` constructs
a coherent `G`, a map
`a : G ⟶ H`, and an isomorphism `β : completionFunctor.obj G ≅ F` such that
`β.hom ≫ α = completionFunctor.map a`. The actual kernel and cokernel of
`a.hom` are killed by `K ^ t`. The bound uses the same `K` that defines the
formal system.

[AffineBoundedCompletion](AffineBoundedCompletion.lean) and
[AffineBoundedEffectivity](AffineBoundedEffectivity.lean) identify the actual
affine candidate completion through the original quotient units.
[BoundedReconstructionGluing](BoundedReconstructionGluing.lean) constructs
the compatible chart subobjects and glues them inside the original
reconstruction pullback, whose ambient module need not be quasicoherent.
[BoundedCandidateUniqueness](BoundedCandidateUniqueness.lean) retains the
algebraic target map and every formal stage; faithfulness of exceptional-ideal
completion is not assumed.

For an independent ideal sheaf `K`, write
`J = idealThickeningIdealSheaf f I`. The separate theorem
`exists_twoIdealAlgebraization` in [TwoIdeal/Effectivity](TwoIdeal/Effectivity.lean)
takes an original `J`-adic system `F`, a coherent `H`, a map
`φ : F ⟶ (completionFunctor X J).obj H`, and
`AdicSystem.DefectsKilled K t φ`. In addition to the complete Noetherian base
and properness hypotheses, it requires
`ClosedThickeningCompletionEssSurj f I K`, namely effectivity on the actual
`K`-power thickenings. It returns `G`, `a : G ⟶ H`, and a specified original
`J`-completion comparison retaining `φ`; both ordinary defects of `a.hom` are
killed by `K ^ (t * 2)`. Its `twoIdeal_mem_essImage` corollary gives effectivity
of `F`. An independent ideal bound alone is not the same-ideal reconstruction
hypothesis. [TwoIdeal/CoefficientSystem](TwoIdeal/CoefficientSystem.lean)
constructs the `K`-adic system from the algebraized independent quotients,
and [TwoIdeal/Recovery](TwoIdeal/Recovery.lean) recovers the entire original
`J`-adic system from the bounded reconstruction while retaining its target
map and transitions.

## Algebra operations and finite-etale covers

[Algebraization/Operations](Algebraization/Operations.lean) defines
`AdicAlgebraStructure F`: native commutative algebra structures on the actual
stages, with the original transitions preserving both operations.
`AdicAlgebraizationData F` retains a coherent algebra, its specified completion
isomorphism, and all original stage-map certificates.
`properAdicAlgebraization I f F` constructs these data under the same proper
existence hypotheses. Coherent full faithfulness lifts the unit and
multiplication; detection on coherent tensor sources proves the algebra laws.
The stage maps are literally the original quotient units followed by the
specified formal comparison.

The [complete-local finite-etale application](../../Morphisms/FiniteEtale/ProperCompleteLocal.md)
uses this algebraization to reconstruct actual covers from their nilpotent
thickening towers. Its additional local and maximal-ideal-completeness
hypotheses belong to that application. Finite-etale cover comparison remains
owned by [Morphisms/FiniteEtale](../../Morphisms/FiniteEtale/README.md).
