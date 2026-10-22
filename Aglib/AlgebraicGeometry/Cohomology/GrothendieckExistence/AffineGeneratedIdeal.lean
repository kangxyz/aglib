/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotient

/-! # Original affine ideal coordinates of a generated ideal sheaf -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u

/-- Generating and then taking original Spec coordinates recovers the same ideal. -/
@[simp]
theorem affineIdeal_idealThickeningIdealSheaf (B : CommRingCat.{u}) (J : Ideal B) :
    affineIdeal B (idealThickeningIdealSheaf (𝟙 (Spec B)) J) = J := by
  simp [affineIdeal, idealThickeningIdealSheaf_ideal, idealThickeningBaseScalar,
    Ideal.map_map, ← CommRingCat.hom_comp]

end AlgebraicGeometry.Scheme.Modules.Coherent
