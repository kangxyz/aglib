/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Coefficient arrows in a coherent horizontal square

Horizontal square coherence and naturality of the original target comparison
prove the full coefficient-arrow equation over variable categories. The
coefficient is appended to the existing square, without changing its maps.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {L₀ : A ⥤ B} {L₁ : C ⥤ D} {L₂ : E ⥤ F}
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {G : A ⥤ E} {H : B ⥤ F}

/-- Appending an original coefficient arrow to the coherent horizontal square
retains exactly the original target-comparison naturality. -/
theorem horizontalSquareEquation_coefficient
    (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
    (α : TwoSquare G L₀ L₂ H) (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)
    (X : A) (Y : B) (c : L₀.obj X ⟶ Y)
    (h : HorizontalSquareEquation α₁ α₂ α γ δ X) :
    L₂.map (γ.app X) ≫ α₂.app (G₁.obj X) ≫
        H₂.map (α₁.app X ≫ H₁.map c) =
      (α.app X ≫ H.map c) ≫ δ.app Y := by
  dsimp only [HorizontalSquareEquation] at h
  have hc := congrArg (fun k => k ≫ H₂.map (H₁.map c)) h
  have hn := δ.naturality c
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc] at hc
  rw [← hn] at hc
  simpa only [Functor.map_comp, Category.assoc] using hc

end CategoryTheory
