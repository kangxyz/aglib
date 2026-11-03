/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# The original function-field map from an isomorphism on a nonempty open

The original open-inclusion field maps and original restricted morphism
identify the function-field map of the given dominant integral morphism.
No properness, normality, Noetherianity or dimension hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The actual generic-point field map is invertible because the two open
inclusions and the original restricted map induce the same field triangle. -/
theorem functionFieldMap_isIso_of_isIso_restrict {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (h : Y ⟶ X) [IsDominant h]
    (U : X.Opens) [Nonempty U] (hU : IsIso (h ∣_ U)) :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h)) := by
  let := hU
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsIntegral (h ⁻¹ᵁ U).toScheme := IsIntegral.of_isIso (inv (h ∣_ U))
  let i := (h ⁻¹ᵁ U).ι
  let : IsDominant i := Scheme.isDominant_of_isOpenImmersion i
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap i)) :=
    Scheme.FunctionField.fieldMap_isIso i
  have : IsOpenImmersion (i ≫ h) := by
    change IsOpenImmersion ((h ⁻¹ᵁ U).ι ≫ h)
    rw [← morphismRestrict_ι]
    infer_instance
  have : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap i)) := by
    rw [← CommRingCat.ofHom_comp, ← Scheme.functionFieldMap_comp]
    exact Scheme.FunctionField.fieldMap_isIso (i ≫ h)
  exact IsIso.of_isIso_comp_right (CommRingCat.ofHom (Scheme.functionFieldMap h))
    (CommRingCat.ofHom (Scheme.functionFieldMap i))

end AlgebraicGeometry.Scheme
