/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineFormalBounds

/-!
# The finite affine module reconstructed from original geometric bounds

The input is an actual formal morphism to completion of an actual coherent
sheaf, with bounded ordinary stage defects. Its original native pullback is
finite over the uncompleted chart ring, and its completion recovers the
original formal-section module with the original first projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H : (Spec B).CoherentSheaf} (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- The formal section target is a module over the completed original coefficient ring. -/
local instance : Module (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineFormalSectionsModule

local instance : IsScalarTower B (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineSections_isCompatibleSystem.sectionsScalarTower

local instance : Module.Finite (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineFormalSections_finite

local instance : Module.Finite B (moduleSpecΓFunctor.obj H.obj) :=
  ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).2

/-- The actual native affine pullback, independent of a chosen bound. -/
abbrev affineReconstructionModule :=
  LinearMap.pullbackKernel ((affineReconstructionMap α).restrictScalars B)
    (AdicCompletion.of (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj))

/-- The original algebraic projection of the affine pullback. -/
abbrev affineReconstructionModuleToTarget :
    affineReconstructionModule α →ₗ[B] moduleSpecΓFunctor.obj H.obj :=
  LinearMap.pullbackKernelSnd ((affineReconstructionMap α).restrictScalars B)
    (AdicCompletion.of (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj))

/-- Actual bounded geometric defects make the original pullback finite over
the uncompleted affine ring. Only the kernel bound is used for finiteness. -/
theorem affineReconstructionModule_finite (t : ℕ) (h : AdicSystem.DefectsKilled K t α) :
    Module.Finite B (affineReconstructionModule α) :=
  AdicCompletion.finite_pullback_of_pow_ker_eq_bot (affineIdeal B K)
    (affineReconstructionMap α) t (affineReconstructionMap_bounds α K t h).1

/-- Both original algebraic defects are bounded by the same ideal power.
This is a property of the original second projection, not of a chosen map. -/
theorem affineReconstructionModuleToTarget_bounds (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    affineIdeal B K ^ t • (affineReconstructionModuleToTarget α).ker = ⊥ ∧
      affineIdeal B K ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj H.obj)) ≤
        (affineReconstructionModuleToTarget α).range :=
  ⟨LinearMap.smul_ker_pullbackKernelSnd_eq_bot _ _ _
      (affineReconstructionMap_bounds α K t h).1,
    LinearMap.smul_top_le_range_pullbackKernelSnd _ _ _
      (affineReconstructionMap_bounds α K t h).2⟩

/-- The actual completion of the finite reconstructed module recovers the
original compatible affine formal sections over the completed ring. -/
def affineReconstructionModuleCompletionEquiv (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    AdicCompletion (affineIdeal B K) (affineReconstructionModule α) ≃ₗ[
      AdicCompletion (affineIdeal B K) B] F.affineFormalSections :=
  AdicCompletion.boundedPullbackCompletionEquiv (affineIdeal B K)
    (affineReconstructionMap α) t (affineReconstructionMap_bounds α K t h).1
      (affineReconstructionMap_bounds α K t h).2

/-- The completion comparison retains the literal original first projection. -/
theorem affineReconstructionModuleCompletionEquiv_of (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) (x : affineReconstructionModule α) :
    affineReconstructionModuleCompletionEquiv α t h
      (AdicCompletion.of (affineIdeal B K) _ x) = x.val.1 :=
  AdicCompletion.boundedPullbackCompletionEquiv_of _ _ _ _ _ x

end AlgebraicGeometry.Scheme.Modules.Coherent
