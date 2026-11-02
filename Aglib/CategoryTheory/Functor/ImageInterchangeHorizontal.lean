/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageInterchangeAssociativity

/-! # Import original horizontal mate laws without concrete component conversion -/

@[expose] public section
namespace CategoryTheory

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {R₀ : B ⥤ A} {R₁ : D ⥤ C} {R₂ : F ⥤ E}
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {G : A ⥤ E} {H : B ⥤ F}
  {L₀ : A ⥤ B} {L₁ : C ⥤ D} {L₂ : E ⥤ F}

/-- Whole original mate identification produces the same horizontal predicate
consumed by the image associativity core. -/
theorem imageHorizontalInterchange_of_mates
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
    (α : TwoSquare G L₀ L₂ H) (γ : G ≅ G₁ ⋙ G₂) (δ : H ≅ H₁ ⋙ H₂)
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β : R₀ ⋙ G ⟶ H ⋙ R₂)
    (hβ₁ : β₁ = (mateEquiv adj₀ adj₁ α₁).natTrans)
    (hβ₂ : β₂ = (mateEquiv adj₁ adj₂ α₂).natTrans)
    (hβ : β = (mateEquiv adj₀ adj₂ α).natTrans)
    (h : ∀ K, HorizontalMateEquation α₁ α₂ α γ.hom δ.hom adj₀ adj₁ adj₂ K) :
    ImageHorizontalInterchange β₁ β₂ β γ δ := by
  intro K
  exact actualHorizontalMateEquation_of_mates adj₀ adj₁ adj₂ α₁ α₂ α γ.hom δ.hom
    β₁ β₂ β hβ₁ hβ₂ hβ K (h K)

end CategoryTheory
