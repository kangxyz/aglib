/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompleteAffineModificationComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompletionDefects

/-! # A single exceptional bound on the original complete affine comparison

Proper full faithfulness lifts the specified upstairs isomorphism. Its actual
algebraic adjoint has one coherent exceptional bound, and independent ordinary
quotients give one doubled bound for all stages of the original comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  (J : Ideal B) [IsAdicComplete J B]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p]
  (M : (Spec B).CoherentSheaf) (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p (𝟙 (Spec B)) J).obj
      ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj M) ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)).obj G)

/-- One positive exceptional exponent kills both ordinary defects at every
stage of the specified affine comparison over a complete base. -/
theorem affineModificationComparison_complete_hasBoundedDefects
    (K : (Spec B).IdealSheafData) (U : (Spec B).Opens) [IsIso (p ∣_ U)]
    (hU : (U : Set (Spec B))ᶜ ⊆ K.support) :
    AdicSystem.HasBoundedDefects K (affineModificationComparison p J _ G β.hom) := by
  obtain ⟨t, ht, hk, hc⟩ :=
    completeBaseModificationAdjoint_bounded J p (𝟙 (Spec B)) M G β K U hU
  rw [affineModificationComparison_eq_completeBaseAdjoint]
  refine ⟨t * 2, Nat.mul_pos ht (by decide), ?_⟩
  exact completionFunctor_map_defectsKilled
    (properCoherentAdjoint p M G
      (completeBaseModificationIso J p (𝟙 (Spec B)) M G β).hom)
    (idealThickeningIdealSheaf (𝟙 (Spec B)) J) K t hk hc

end AlgebraicGeometry.Scheme.Modules.Coherent
