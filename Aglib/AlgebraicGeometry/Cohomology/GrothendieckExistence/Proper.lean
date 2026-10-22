/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ChowSourceEffectivity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalModificationBoundedComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.Effectivity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.IdealInduction

/-! # Grothendieck existence for an actual proper morphism

Ideal-sheaf Noetherian induction preserves nilpotent structure. The original
Chow modification supplies a projective realization; the original bounded
formal comparison and two-ideal reconstruction descend it. The final forward
functor is literally coherent completion for the original base ideal.
-/

@[expose] public noncomputable section
open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Original coherent completion is essentially surjective for an actual
proper morphism over a complete Noetherian base. Local Noetherianity is derived. -/
theorem properCompletionEssSurj :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (idealThickeningIdealSheaf f I)).EssSurj := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let P : X.IdealSheafData → Prop := fun K =>
    let : IsLocallyNoetherian K.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian K.subschemeι
    (completionFunctor K.subscheme
      (idealThickeningIdealSheaf (K.subschemeι ≫ f) I)).EssSurj
  have hP : ∀ K, P K := by
    intro K
    induction K using WellFoundedGT.induction with
    | ind K ih =>
      let : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian K.subschemeι
      change (completionFunctor K.subscheme
        (idealThickeningIdealSheaf (K.subschemeι ≫ f) I)).EssSurj
      by_cases hK : Nonempty K.subscheme
      · let := hK
        refine ⟨fun F => ?_⟩
        obtain ⟨Y, p, V, hp, _, hV, hpV, hY, G, ⟨β⟩⟩ :=
          exists_chowSource_realization A I (K.subschemeι ≫ f) F
        let : IsProper p := hp
        let : IsIso (p ∣_ V) := hpV
        let : IsLocallyNoetherian Y := hY
        let J := IdealSheafData.vanishingIdeal
          (⟨(V : Set K.subscheme)ᶜ, V.isOpen.isClosed_compl⟩ :
            TopologicalSpace.Closeds K.subscheme)
        have hJS : (J.support : Set K.subscheme) = (V : Set K.subscheme)ᶜ :=
          IdealSheafData.coe_support_vanishingIdeal _
        have hJ : Dense (J.support : Set K.subscheme)ᶜ := by
          rw [hJS, compl_compl]
          exact hV
        have hclosed := closedThickeningCompletionEssSurj_of_idealInduction I f K
          (fun L hL => ih L hL) J hJ
        have hsupport : (V : Set K.subscheme)ᶜ ⊆ J.support := hJS.ge
        obtain ⟨φ, _, t, _, ht⟩ := exists_formalModificationComparison_bounded p
          (K.subschemeι ≫ f) I F G β J V hsupport
        exact twoIdeal_mem_essImage I (K.subschemeι ≫ f) J hclosed F φ t ht
      · let : IsEmpty K.subscheme := not_nonempty_iff.mp hK
        exact completionFunctorEssSurjOfIsEmpty K.subscheme
          (idealThickeningIdealSheaf (K.subschemeι ≫ f) I)
  have he := completionEssSurjOfKernelImage I (𝟙 X) f (hP _)
  have hid : (𝟙 X) ≫ f = f := Category.id_comp f
  exact (congrArg (fun g : X ⟶ Spec (CommRingCat.of A) =>
    (completionFunctor X (idealThickeningIdealSheaf g I)).EssSurj) hid).mp he

/-- Every original coherent adic system on a proper scheme is algebraizable. -/
theorem proper_completion_essImage :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ F : AdicSystem X (idealThickeningIdealSheaf f I),
      (completionFunctor X (idealThickeningIdealSheaf f I)).essImage F := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := properCompletionEssSurj I f
  exact Functor.EssSurj.mem_essImage _

/-- Grothendieck existence for the original proper morphism, without auxiliary
flatness, locality, projectivity, dimension or realization assumptions. -/
theorem properCompletionIsEquivalence :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (idealThickeningIdealSheaf f I)).IsEquivalence := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact {
    faithful := (completionFunctorFullyFaithful I f).faithful
    full := (completionFunctorFullyFaithful I f).full
    essSurj := properCompletionEssSurj I f }

/-- Proper coherent Grothendieck existence with native completion as forward functor. -/
def properCompletionEquivalence :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    X.CoherentSheaf ≌ AdicSystem X (idealThickeningIdealSheaf f I) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := properCompletionIsEquivalence I f
  exact (completionFunctor X (idealThickeningIdealSheaf f I)).asEquivalence

/-- The proper equivalence's forward functor is literally original completion. -/
theorem properCompletionEquivalence_functor :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (properCompletionEquivalence I f).functor =
      completionFunctor X (idealThickeningIdealSheaf f I) := rfl

end AlgebraicGeometry.Scheme.Cohomology
