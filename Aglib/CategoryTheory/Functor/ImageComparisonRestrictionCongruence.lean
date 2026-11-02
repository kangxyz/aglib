/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageComparisonRestriction

/-! # Restriction of original image maps through whole input identifications -/

@[expose] public section
namespace CategoryTheory
variable {U U' A B T : Type*}
  [Category* U] [Category* U'] [Category* A] [Category* B] [Category* T]
  {L₁ : U ⥤ A} {L₂ : U ⥤ B} {R₁ : A ⥤ T} {R₂ : B ⥤ T} {F : A ⥤ B}

/-- Whole original unit and structural comparisons can be identified before source restriction. -/
theorem imageComparison_whiskerLeft_of_eq (V : U' ⥤ U)
    (δ₀ δ : L₂ ⟶ L₁ ⋙ F) (e₀ e : F ⋙ R₂ ≅ R₁)
    (hδ : δ₀ = δ) (he : e₀ = e) :
    Functor.whiskerLeft V (imageComparison δ₀ e₀) =
      imageComparison (L₁ := V ⋙ L₁) (L₂ := V ⋙ L₂)
        (R₁ := R₁) (R₂ := R₂) (F := F) (Functor.whiskerLeft V δ) e := by
  subst δ₀
  subst e₀
  exact imageComparison_whiskerLeft V δ e

end CategoryTheory
