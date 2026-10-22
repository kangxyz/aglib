/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineGeneratedIdeal
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BaseIdealScalarExtension
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BaseIdealPullback

/-! # Original affine ideals after arbitrary scalar base change -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u

/-- Pulling back any affine ideal sheaf extends its original coordinate ideal. -/
theorem affineIdeal_comap_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (K : (Spec R).IdealSheafData) :
    affineIdeal S (K.comap (Spec.map φ)) = Ideal.map φ.hom (affineIdeal R K) := by
  calc
    _ = affineIdeal S
        ((idealThickeningIdealSheaf (𝟙 (Spec R)) (affineIdeal R K)).comap (Spec.map φ)) := by
      rw [idealThickeningIdealSheaf_affineIdeal]
    _ = affineIdeal S
        (idealThickeningIdealSheaf (Spec.map φ) (affineIdeal R K)) := by
      rw [baseIdeal_comap, Category.comp_id]
    _ = _ := by
      rw [idealThickeningIdealSheaf_specMap, affineIdeal_idealThickeningIdealSheaf]

end AlgebraicGeometry.Scheme.Modules.Coherent
