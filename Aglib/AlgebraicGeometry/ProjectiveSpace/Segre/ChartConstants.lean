/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.Sections

/-!
# Original structural constants evaluated on affine charts
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Segre

set_option backward.isDefEq.respectTransparency false in
/-- Structural coefficients evaluate by the original affine-chart base ring map. -/
theorem chart_pullback_constant {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (b : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens)
    (B : CommRingCat.{u}) (j : Spec B ⟶ Y) (hj : ⊤ ≤ j ⁻¹ᵁ U)
    (c : CommRingCat.of R ⟶ B) (hc : j ≫ b = Spec.map c) (r : R) :
    (j.appLE U ⊤ hj ≫ (Scheme.ΓSpecIso B).hom) (structuralCoefficient b U r) = c r := by
  have he : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      b.appLE ⊤ U le_top ≫ j.appLE U ⊤ hj ≫ (Scheme.ΓSpecIso B).hom = c := by
    rw [← Category.assoc (b.appLE ⊤ U le_top),
      Scheme.Hom.appLE_comp_appLE j b ⊤ U ⊤ le_top hj]
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (j ≫ b).appTop ≫ (Scheme.ΓSpecIso B).hom = c
    rw [hc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom he r

end AlgebraicGeometry.ProjectiveSpace.Segre
