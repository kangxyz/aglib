/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedCompletion
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineFormalIso

/-! # Effectivity of the original affine bounded reconstruction -/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H : (Spec B).CoherentSheaf} (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- The constructed completion map is an isomorphism in the original formal
category, by its equality with the bounded native pullback equivalence. -/
theorem affineReconstructionCompletionMap_isIso (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    IsIso (affineReconstructionCompletionMap α t h) := by
  let G := affineReconstructionSheaf α t h
  let := F.affineFormalSectionsModule
  let := ((completionFunctor (Spec B) K).obj G).affineFormalSectionsModule
  let e := (AdicCompletion.congr (affineIdeal B K)
    (tilde.toTildeΓNatIso.app (ModuleCat.of B (affineReconstructionModule α))).toLinearEquiv).trans
      (affineCompletionSectionsEquiv B K G)
  apply AdicSystem.isIso_of_affineFormalSectionsMap_bijective
  apply (Function.Bijective.of_comp_iff _ e.bijective).mp
  change Function.Bijective (affineReconstructionCompletionSectionsMap α t h)
  rw [affineReconstructionCompletionSectionsMap_eq]
  exact (affineReconstructionModuleCompletionEquiv α t h).bijective

/-- An affine formal system with an actual bounded map to completion is
algebraized by the actual finite pullback, with the original projection square. -/
def affineReconstructionCompletionIso (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    (completionFunctor (Spec B) K).obj (affineReconstructionSheaf α t h) ≅ F := by
  let := affineReconstructionCompletionMap_isIso α t h
  exact asIso (affineReconstructionCompletionMap α t h)

end AlgebraicGeometry.Scheme.Modules.Coherent
