/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineModificationComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompleteBaseModification
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalAlgebraicAdjunction

/-! # The actual affine comparison over a complete base

For an algebraized source over a complete affine base, the original affine
formal-functions construction is exactly completion of the algebraic adjoint
of the specified full-faithful lift. This is not yet transport from an
uncompleted affine chart to its completed base.
-/

@[expose] public noncomputable section
open CategoryTheory
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

/-- The original affine comparison is completion of the specific algebraic adjoint. -/
theorem affineModificationComparison_eq_completeBaseAdjoint :
    affineModificationComparison p J _ G β.hom =
      (completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).map
        (properCoherentAdjoint p M G
          (completeBaseModificationIso J p (𝟙 (Spec B)) M G β).hom) := by
  symm
  apply affineModificationComparison_original_unique
  have h := formalAlgebraicAdjoint_diagram p (𝟙 (Spec B)) J M G
    (completeBaseModificationIso J p (𝟙 (Spec B)) M G β).hom
  rw [completeBaseModificationIso_completion] at h
  exact h

end AlgebraicGeometry.Scheme.Modules.Coherent
