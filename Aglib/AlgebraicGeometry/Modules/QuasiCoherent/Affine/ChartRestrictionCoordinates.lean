/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Chart

/-! # Original affine-chart section coordinates under restriction -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}} (M : X.Modules)

/-- The inverse chart comparison is the original transport along the chart-image equality. -/
theorem affineChartΓIso_inv_apply (U : X.affineOpens) (m : Γ(M, U)) :
    (affineChartΓIso U M).inv m = M.presheaf.map
      (eqToHom (show U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U.val from by
        simp [Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec])).op m := rfl

/-- The original inverse chart coordinates preserve every affine restriction. -/
theorem affineChartΓIso_inv_restrict (U V : X.affineOpens) (i : V.val ⟶ U.val)
    (h : V.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) ≤
      U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) (m : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op ((affineChartΓIso U M).inv m) =
      (affineChartΓIso V M).inv (M.presheaf.map i.op m) := by
  rw [affineChartΓIso_inv_apply, affineChartΓIso_inv_apply]
  simp only [← Functor.map_comp_apply]
  congr 1

end AlgebraicGeometry.Scheme.Modules
