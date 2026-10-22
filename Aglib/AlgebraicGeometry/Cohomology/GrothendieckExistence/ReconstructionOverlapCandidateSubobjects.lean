/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionOverlapComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionOverlapSubobjects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionMappedExt

/-! # Original ambient compatibility before specializing reconstructed charts -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- Whole algebraic candidate compatibility forces the original ambient square. -/
def reconstructionOverlapAmbientComparisonOfCandidates
    {X U V : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (p : U ⟶ X) (q : V ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q]
    {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}
    (α : F ⟶ (completionFunctor X K).obj H)
    {G₁ : U.CoherentSheaf} {G₂ : V.CoherentSheaf}
    (a₁ : G₁ ⟶ (coherentPullback p).obj H)
    (β₁ : (completionFunctor U (K.comap p)).obj G₁ ≅
      (openIdealPullbackFunctor p K).obj F)
    (s₁ : G₁.obj ⟶ (pullback p).obj (reconstructionPullback α))
    (ht₁ : s₁ ≫ (pullback p).map (reconstructionToTarget α) = a₁.hom)
    (hs₁ : ∀ n : ℕᵒᵖ, s₁ ≫ (pullback p).map (reconstructionToStage α n) =
      (idealSheafQuotientUnit U (K.comap p ^ n.unop)).app G₁.obj ≫ β₁.hom.hom.app n)
    (a₂ : G₂ ⟶ (coherentPullback q).obj H)
    (β₂ : (completionFunctor V (K.comap q)).obj G₂ ≅
      (openIdealPullbackFunctor q K).obj F)
    (s₂ : G₂.obj ⟶ (pullback q).obj (reconstructionPullback α))
    (ht₂ : s₂ ≫ (pullback q).map (reconstructionToTarget α) = a₂.hom)
    (hs₂ : ∀ n : ℕᵒᵖ, s₂ ≫ (pullback q).map (reconstructionToStage α n) =
      (idealSheafQuotientUnit V (K.comap q ^ n.unop)).app G₂.obj ≫ β₂.hom.hom.app n)
    (d : reconstructionOverlapCandidateComparison p q a₁ β₁ a₂ β₂) :
    ReconstructionOverlapAmbientComparison p q s₁ s₂ := by
  refine ⟨(QuasiCoherent.finiteTypeSheavesToModules (Limits.pullback p q)).mapIso d.val, ?_⟩
  let : PreservesLimitsOfShape ℕᵒᵖ (pullback q) :=
    preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback q)
  let : PreservesLimitsOfShape ℕᵒᵖ (pullback (pullback.snd p q)) :=
    preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback (pullback.snd p q))
  let : PreservesLimitsOfShape WalkingCospan (pullback q) :=
    preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback q)
  let : PreservesLimitsOfShape WalkingCospan (pullback (pullback.snd p q)) :=
    preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback (pullback.snd p q))
  apply reconstructionMapped_hom_ext (pullback q ⋙ pullback (pullback.snd p q)) α
  · rw [Category.assoc, ← (reconstructionOverlapPullbackIso p q).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc, ht₁, ht₂,
      Category.assoc, ← Functor.map_comp]
    exact d.property.1.symm
  · rintro ⟨n⟩
    rw [Category.assoc, ← (reconstructionOverlapPullbackIso p q).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc, hs₁, hs₂,
      Category.assoc, ← Functor.map_comp]
    exact (d.property.2 n).symm

end AlgebraicGeometry.Scheme.Modules.Coherent
