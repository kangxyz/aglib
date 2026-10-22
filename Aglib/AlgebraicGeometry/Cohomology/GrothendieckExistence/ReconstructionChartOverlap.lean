/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionChart
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionOverlapCandidateSubobjects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionOverlapComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionOverlapSubobjects

/-! # Actual chart subobjects agree on arbitrary overlaps -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {B C : CommRingCat.{u}} [IsNoetherianRing B] [IsNoetherianRing C]
  (p : Spec B ⟶ X) (q : Spec C ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (t : ℕ) (h : AdicSystem.DefectsKilled K t α)

/-- The actual chart completion isomorphism, before any overlap restriction. -/
abbrev reconstructionChartCompletionIso :
    (completionFunctor (Spec B) (K.comap p)).obj (reconstructionChart p α t h) ≅
      (openIdealPullbackFunctor p K).obj F :=
  affineReconstructionCompletionIso (openReconstructionComparison p α) t
    (openReconstructionComparison_defectsKilled p α K t h)

/-- Its quotient-unit equation gives the original chart stages. -/
@[reassoc]
theorem reconstructionChartCompletionIso_stage (n : ℕ) :
    (idealSheafQuotientUnit (Spec B) (K.comap p ^ n)).app
        (reconstructionChart p α t h).obj ≫
      (reconstructionChartCompletionIso p α t h).hom.hom.app (op n) =
        (reconstructionChartStages p α t h).app (op n) :=
  idealSheafQuotientUnit_desc (Spec B) (K.comap p ^ n)
    ((reconstructionChartStages p α t h).app (op n))
      (((openIdealPullbackFunctor p K).obj F).property.annihilated n)

local instance : IsLocallyNoetherian (Limits.pullback p q) :=
  isLocallyNoetherian_of_isOpenImmersion (pullback.fst p q)

/-- The genuine overlap comparison retains the original ambient inclusion. -/
def reconstructionChartOverlapPullback :
    ReconstructionOverlapAmbientComparison p q
      (reconstructionChartLift p α t h) (reconstructionChartLift q α t h) := by
  let d := reconstructionOverlapCandidateIso p q α
    (reconstructionChartTarget p α t h) (reconstructionChartCompletionIso p α t h)
    (affineReconstructionCompletionMap_comp (openReconstructionComparison p α) t
      (openReconstructionComparison_defectsKilled p α K t h)) t
    (affineReconstructionSheafMap_bounds (openReconstructionComparison p α) t
      (openReconstructionComparison_defectsKilled p α K t h)).1
    (affineReconstructionSheafMap_bounds (openReconstructionComparison p α) t
      (openReconstructionComparison_defectsKilled p α K t h)).2
    (reconstructionChartTarget q α t h) (reconstructionChartCompletionIso q α t h)
    (affineReconstructionCompletionMap_comp (openReconstructionComparison q α) t
      (openReconstructionComparison_defectsKilled q α K t h)) t
    (affineReconstructionSheafMap_bounds (openReconstructionComparison q α) t
      (openReconstructionComparison_defectsKilled q α K t h)).1
    (affineReconstructionSheafMap_bounds (openReconstructionComparison q α) t
      (openReconstructionComparison_defectsKilled q α K t h)).2
  refine reconstructionOverlapAmbientComparisonOfCandidates p q α
    (reconstructionChartTarget p α t h) (reconstructionChartCompletionIso p α t h)
    (reconstructionChartLift p α t h) (reconstructionChartLift_toTarget p α t h) ?_
    (reconstructionChartTarget q α t h) (reconstructionChartCompletionIso q α t h)
    (reconstructionChartLift q α t h) (reconstructionChartLift_toTarget q α t h) ?_ d
  · rintro ⟨n⟩
    rw [reconstructionChartLift_toStage, reconstructionChartCompletionIso_stage]
  · rintro ⟨n⟩
    rw [reconstructionChartLift_toStage, reconstructionChartCompletionIso_stage]

/-- The chart subobjects agree in the exact native restriction coordinates
required by coherent finite-cover subobject gluing. -/
def reconstructionChartOverlap :
    ReconstructionOverlapRestrictionComparison p q
      (reconstructionChartLift p α t h) (reconstructionChartLift q α t h) :=
  reconstructionOverlapRestrictionComparison p q
    (reconstructionChartLift p α t h) (reconstructionChartLift q α t h)
    (reconstructionChartOverlapPullback p q α t h)

end AlgebraicGeometry.Scheme.Modules.Coherent
