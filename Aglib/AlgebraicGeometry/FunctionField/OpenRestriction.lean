/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.FunctionField.StalkMap

/-! # Actual scalars under open restriction

The inverse of the original section-ring isomorphism of an open immersion
identifies scalar germs through the original function-field map. Nonempty
opens are retained because their generic-value maps are used; empty-open
module comparisons must instead use their subsingleton section modules.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FunctionField

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
  (j : U ⟶ X) [IsOpenImmersion j]

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- The actual scalar of an open-restricted module has the same generic value
under the actual map between function fields. -/
theorem map_germ_appIso_inv (V : U.Opens) [Nonempty V] [Nonempty (j ''ᵁ V)]
    (a : Γ(U, V)) :
    Scheme.functionFieldMap j
      (X.germToFunctionField (j ''ᵁ V) ((j.appIso V).inv a)) =
      U.germToFunctionField V a := by
  obtain ⟨x, hx⟩ := (inferInstance : Nonempty V)
  have hjx : j x ∈ j ''ᵁ V := ⟨x, hx, rfl⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hjx,
    Scheme.functionFieldMap_stalk, Scheme.Hom.germ_stalkMap_apply,
    Scheme.Hom.appIso_inv_app_apply]
  have hp : x ∈ j ⁻¹ᵁ (j ''ᵁ V) := hjx
  exact (congrArg (algebraMap (U.presheaf.stalk x) U.functionField)
    (U.presheaf.germ_res_apply (eqToHom (j.preimage_image_eq V)) x hp a)).trans
      (Scheme.algebraMap_germ_eq_germToFunctionField U hx a)

end AlgebraicGeometry.Scheme.FunctionField
