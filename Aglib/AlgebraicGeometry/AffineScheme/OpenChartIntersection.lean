/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.OpenImmersionIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Original affine charts on an affine open intersection -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} (U V W : X.affineOpens)
  (hWU : W.val ≤ U.val) (hWV : W.val ≤ V.val) (hW : W.val = U.val ⊓ V.val)

include hW in
/-- The actual affine chart of an intersection gives the original cartesian
square of affine-chart restriction maps. -/
theorem affineOpenIntersection_isPullback :
    IsPullback (Spec.map (X.presheaf.map (homOfLE hWU).op))
      (Spec.map (X.presheaf.map (homOfLE hWV).op)) U.property.fromSpec V.property.fromSpec := by
  have ha := U.property.map_fromSpec W.property (homOfLE hWU).op
  have hb := V.property.map_fromSpec W.property (homOfLE hWV).op
  have : IsOpenImmersion
      (Spec.map (X.presheaf.map (homOfLE hWU).op) ≫ U.property.fromSpec) := by
    rw [ha]
    infer_instance
  have : IsOpenImmersion
      (Spec.map (X.presheaf.map (homOfLE hWV).op) ≫ V.property.fromSpec) := by
    rw [hb]
    infer_instance
  have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hWU).op)) :=
    IsOpenImmersion.of_comp _ U.property.fromSpec
  have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hWV).op)) :=
    IsOpenImmersion.of_comp _ V.property.fromSpec
  apply isPullback_of_openImmersion_range_inter W.property.fromSpec _ _ _ _ ha hb
  rw [W.property.range_fromSpec, U.property.range_fromSpec, V.property.range_fromSpec, hW]
  rfl

end AlgebraicGeometry.Scheme
