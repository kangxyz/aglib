/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionMappedLift
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenReconstructionStages
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedMonicity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenFormalDefects

/-! # Actual coherent chart subobjects of the original reconstruction pullback

The ambient sheaf is the original global reconstruction pullback. It need not
be quasicoherent. Monicity follows by factoring a finite-stage monomorphism,
not by applying global sections to an arbitrary ambient module sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {B : CommRingCat.{u}} [IsNoetherianRing B]
  (p : Spec B ⟶ X) [IsOpenImmersion p]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (t : ℕ) (h : AdicSystem.DefectsKilled K t α)

local instance : PreservesLimitsOfShape ℕᵒᵖ (pullback p) :=
  preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback p)

local instance : PreservesLimitsOfShape WalkingCospan (pullback p) :=
  preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback p)

/-- The actual coherent local coefficient on an affine chart. -/
abbrev reconstructionChart : (Spec B).CoherentSheaf :=
  affineReconstructionSheaf (openReconstructionComparison p α) t
    (openReconstructionComparison_defectsKilled p α K t h)

/-- Its original algebraic projection. -/
abbrev reconstructionChartTarget :
    reconstructionChart p α t h ⟶ (coherentPullback p).obj H :=
  affineReconstructionSheafMap (openReconstructionComparison p α) t
    (openReconstructionComparison_defectsKilled p α K t h)

/-- Its original compatible formal projections. -/
abbrev reconstructionChartStages :
    (Functor.const ℕᵒᵖ).obj (reconstructionChart p α t h).obj ⟶ F.obj ⋙ pullback p :=
  affineReconstructionSheafStages (openReconstructionComparison p α) t
    (openReconstructionComparison_defectsKilled p α K t h)

/-- The local square also holds before changing the target quotient coordinates. -/
theorem reconstructionChartStages_square (n : ℕᵒᵖ) :
    ReconstructionStageSquare ((reconstructionChartStages p α t h).app n)
      ((pullback p).map (α.hom.app n)) (reconstructionChartTarget p α t h).hom
      ((pullback p).map ((idealSheafQuotientUnit X (K ^ n.unop)).app H.obj)) :=
  openReconstructionStages_square p α (reconstructionChart p α t h).obj
    (reconstructionChartTarget p α t h).hom (reconstructionChartStages p α t h)
    (affineReconstructionSheafStages_comp (openReconstructionComparison p α) t
      (openReconstructionComparison_defectsKilled p α K t h)) n

/-- The local candidate lies inside the pullback of the original global ambient. -/
def reconstructionChartLift :
    (reconstructionChart p α t h).obj ⟶ (pullback p).obj (reconstructionPullback α) :=
  reconstructionMappedLift (pullback p) α (reconstructionChartTarget p α t h).hom
    (reconstructionChartStages p α t h) (reconstructionChartStages_square p α t h)

@[reassoc (attr := simp)]
theorem reconstructionChartLift_toTarget :
    reconstructionChartLift p α t h ≫ (pullback p).map (reconstructionToTarget α) =
      (reconstructionChartTarget p α t h).hom :=
  reconstructionMappedLift_toTarget _ _ _ _ _

@[reassoc (attr := simp)]
theorem reconstructionChartLift_toStage (n : ℕᵒᵖ) :
    reconstructionChartLift p α t h ≫ (pullback p).map (reconstructionToStage α n) =
      (reconstructionChartStages p α t h).app n :=
  reconstructionMappedLift_toStage _ _ _ _ _ n

/-- Factor the actual finite-stage monomorphism through the ambient inclusion. -/
theorem reconstructionChartLift_mono : Mono (reconstructionChartLift p α t h) := by
  obtain ⟨n, hn⟩ := affineReconstructionSheafStages_jointly_monic
    (openReconstructionComparison p α) t
    (openReconstructionComparison_defectsKilled p α K t h)
  let b : (pullback p).obj (reconstructionPullback α) ⟶ ((coherentPullback p).obj H).obj :=
    (pullback p).map (reconstructionToTarget α)
  let c : (pullback p).obj (reconstructionPullback α) ⟶
      ((openIdealPullbackFunctor p K).obj F).obj.obj (op n) :=
    (pullback p).map (reconstructionToStage α (op n))
  apply @mono_of_mono_fac _ _ _ _ _ (prod.lift b c) (reconstructionChartLift p α t h) _ hn
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst]
    exact reconstructionChartLift_toTarget p α t h
  · simp only [Category.assoc, prod.lift_snd]
    exact reconstructionChartLift_toStage p α t h (op n)

/-- The same genuine subobject, in the restriction coordinates used by gluing. -/
def reconstructionChartInclusion :
    (reconstructionChart p α t h).obj ⟶ (reconstructionPullback α).restrict p :=
  reconstructionChartLift p α t h ≫
    (restrictFunctorIsoPullback p).inv.app (reconstructionPullback α)

/-- The reconstructed chart maps injectively into the original pullback module. -/
instance instMonoReconstructionChartInclusion : Mono (reconstructionChartInclusion p α t h) := by
  have : Mono (reconstructionChartLift p α t h) := reconstructionChartLift_mono p α t h
  dsimp only [reconstructionChartInclusion]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent
