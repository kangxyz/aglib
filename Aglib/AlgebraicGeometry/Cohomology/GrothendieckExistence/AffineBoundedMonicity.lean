/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedEffectivity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedDefects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCandidateMonicity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionPullback

/-! # Monicity of the actual affine bounded reconstruction inclusion

A finite-stage quasicoherent pair detects monicity. The target reconstruction
pullback need not be quasicoherent, and global sections are not asserted to
reflect monomorphisms into arbitrary module sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H : (Spec B).CoherentSheaf} (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- The actual coherent local coefficient maps to the actual sheaf pullback,
retaining its original algebraic and every original formal projection. -/
def affineReconstructionSheafLift (t : ℕ) (h : AdicSystem.DefectsKilled K t α) :
    (affineReconstructionSheaf α t h).obj ⟶ reconstructionPullback α :=
  reconstructionLift α (affineReconstructionSheafMap α t h).hom
    (affineReconstructionSheafStages α t h)
    (affineReconstructionSheafStages_comp α t h)

/-- One actual finite-stage pair already detects the local coefficient. -/
theorem affineReconstructionSheafStages_jointly_monic (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    ∃ n : ℕ, Mono (prod.lift (affineReconstructionSheafMap α t h).hom
      ((affineReconstructionSheafStages α t h).app (op n))) := by
  obtain ⟨n, hn⟩ := affineCandidateStages_jointly_monic
    (affineReconstructionSheafMap α t h) (affineReconstructionCompletionIso α t h) t
    (affineReconstructionSheafMap_bounds α t h).1
  refine ⟨n, ?_⟩
  have hu : (idealSheafQuotientUnit (Spec B) (K ^ n)).app
      (affineReconstructionSheaf α t h).obj ≫
      (affineReconstructionCompletionMap α t h).hom.app (op n) =
        (affineReconstructionSheafStages α t h).app (op n) :=
    idealSheafQuotientUnit_desc (Spec B) (K ^ n)
      ((affineReconstructionSheafStages α t h).app (op n)) (F.property.annihilated n)
  change Mono (prod.lift (affineReconstructionSheafMap α t h).hom
    ((idealSheafQuotientUnit (Spec B) (K ^ n)).app
      (affineReconstructionSheaf α t h).obj ≫
      (affineReconstructionCompletionMap α t h).hom.app (op n))) at hn
  rwa [hu] at hn

/-- The actual inclusion is mono by factorization of a genuine finite-stage
monomorphism, not by reflection of monicity into the arbitrary ambient limit. -/
theorem affineReconstructionSheafLift_mono (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) : Mono (affineReconstructionSheafLift α t h) := by
  obtain ⟨n, hn⟩ := affineReconstructionSheafStages_jointly_monic α t h
  apply @mono_of_mono_fac _ _ _ _ _
    (prod.lift (reconstructionToTarget α) (reconstructionToStage α (op n)))
    (affineReconstructionSheafLift α t h) _ hn
  apply prod.hom_ext
  · simp [affineReconstructionSheafLift]
  · simp [affineReconstructionSheafLift]

end AlgebraicGeometry.Scheme.Modules.Coherent
