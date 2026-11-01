/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Localization.Adjunction
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-! # The original mate of localization factors

The specified right localization factor is the actual mate of the inverse
left factor. This follows from the original localized unit, on every object
of the original category, without a conservativity or completeness assumption.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

universe uC₁ vC₁ uC₂ vC₂ uD₁ vD₁ uD₂ vD₂

variable {C₁ : Type uC₁} [Category.{vC₁} C₁] {C₂ : Type uC₂} [Category.{vC₂} C₂]
  {D₁ : Type uD₁} [Category.{vD₁} D₁] {D₂ : Type uD₂} [Category.{vD₂} D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)
  [CatCommSq G L₁ L₂ G'] [CatCommSq F L₂ L₁ F']

/-- The original factor of the right adjoint is the mate of the original
inverse factor of the left adjoint. -/
theorem localization_factor_mate :
    (mateEquiv adj (adj.localization L₁ W₁ L₂ W₂ G' F')
      (TwoSquare.mk _ _ _ _ (CatCommSq.iso G L₁ L₂ G').inv)).natTrans =
      (CatCommSq.iso F L₂ L₁ F').hom := by
  apply mateEquiv_inv_natTrans_eq_of_unit
  intro X
  exact (adj.localization_unit_app L₁ W₁ L₂ W₂ G' F' X).symm

end CategoryTheory.Adjunction
