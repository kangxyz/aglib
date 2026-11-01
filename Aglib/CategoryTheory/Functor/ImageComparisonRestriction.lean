/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.CategoryTheory.Functor.ImageComparison

/-! # Source restriction of the original image comparison -/

@[expose] public section
namespace CategoryTheory
variable {U U' A B T : Type*}
  [Category* U] [Category* U'] [Category* A] [Category* B] [Category* T]
  {L₁ : U ⥤ A} {L₂ : U ⥤ B} {R₁ : A ⥤ T} {R₂ : B ⥤ T} {F : A ⥤ B}

/-- Source restriction preserves the actual unit and actual structural image isomorphism. -/
theorem imageComparison_whiskerLeft (V : U' ⥤ U)
    (δ : L₂ ⟶ L₁ ⋙ F) (e : F ⋙ R₂ ≅ R₁) :
    Functor.whiskerLeft V (imageComparison δ e) =
      imageComparison (L₁ := V ⋙ L₁) (L₂ := V ⋙ L₂)
        (R₁ := R₁) (R₂ := R₂) (F := F) (Functor.whiskerLeft V δ) e := by
  apply NatTrans.ext
  funext K
  simp only [Functor.whiskerLeft_app, imageComparison_app, Functor.comp_obj]

end CategoryTheory
