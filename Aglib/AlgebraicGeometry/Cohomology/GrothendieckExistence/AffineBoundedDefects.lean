/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedCompletion
public import Aglib.LinearAlgebra.DefectIdealBound

/-! # The actual algebraic defects of the affine reconstruction

The bounded second projection retains its bounds after passage through the
native tilde unit. These algebraic bounds, not merely an isomorphism of
completions, are the input for uniqueness on affine overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H : (Spec B).CoherentSheaf} (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- Both ordinary defects of the original algebraic reconstruction projection
are killed by the same original ideal power. -/
theorem affineReconstructionSheafMap_bounds (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    killedByIdealSheaf (K ^ t) (kernel (affineReconstructionSheafMap α t h).hom) ∧
      killedByIdealSheaf (K ^ t) (cokernel (affineReconstructionSheafMap α t h).hom) := by
  let G := affineReconstructionSheaf α t h
  let : G.obj.IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B G.obj).mp G.property).1
  let : H.obj.IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).1
  let P := ModuleCat.of B (affineReconstructionModule α)
  let e := (tilde.toTildeΓNatIso.app P).toLinearEquiv
  let b := (moduleSpecΓFunctor.map (affineReconstructionSheafMap α t h).hom).hom
  have he : b.comp e.toLinearMap = affineReconstructionModuleToTarget α := by
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (tildeUnit_sectionsMap_counit P H.obj
        (affineReconstructionTargetHom α)) x
  have hb := LinearMap.defectBounds_of_equiv
    (affineReconstructionModuleToTarget α) b e (LinearEquiv.refl B _)
    (fun x => LinearMap.congr_fun he x) (affineIdeal B K ^ t)
    (affineReconstructionModuleToTarget_bounds α t h).1
    (affineReconstructionModuleToTarget_bounds α t h).2
  exact ⟨killed_kernel_of_affineSections_bound (affineReconstructionSheafMap α t h).hom
      K t hb.1,
    killed_cokernel_of_affineSections_bound (affineReconstructionSheafMap α t h).hom
      K t hb.2⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
