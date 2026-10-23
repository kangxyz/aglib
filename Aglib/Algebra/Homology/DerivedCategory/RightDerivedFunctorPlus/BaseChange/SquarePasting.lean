/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Normalization

/-!
# Shared formulas for horizontal exchange pasting

The definitions retain the literal comparison equations. The proof uses native
mate composition and a supplied, proved square-coherence witness.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {L₀ : A ⥤ B} {R₀ : B ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
  {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {G : A ⥤ E} {H : B ⥤ F}
  (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
  (α : TwoSquare G L₀ L₂ H) (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)

/-- Literal horizontal square coherence with its chosen comparison maps. -/
def HorizontalSquareEquation (X : A) : Prop :=
  L₂.map (γ.app X) ≫ α₂.app (G₁.obj X) ≫ H₂.map (α₁.app X) =
    α.app X ≫ δ.app (L₀.obj X)

/-- Literal horizontal exchange coherence under the actual three adjunctions. -/
def HorizontalMateEquation (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (K : B) : Prop :=
  γ.app (R₀.obj K) ≫ G₂.map ((mateEquiv adj₀ adj₁ α₁).app K) ≫
      (mateEquiv adj₁ adj₂ α₂).app (H₁.obj K) =
    (mateEquiv adj₀ adj₂ α).app K ≫ R₂.map (δ.app K)

/-- Native mate pasting transfers an actual square-coherence witness. -/
theorem horizontalMateEquation (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (h : ∀ X, HorizontalSquareEquation α₁ α₂ α γ δ X) (K : B) :
    HorizontalMateEquation α₁ α₂ α γ δ adj₀ adj₁ adj₂ K := by
  have hα : ∀ X, L₂.map (γ.app X) ≫ (TwoSquare.hComp α₁ α₂).app X =
      α.app X ≫ δ.app (L₀.obj X) := by
    intro X
    simpa only [HorizontalSquareEquation, TwoSquare.hComp_app] using h X
  have hm := mateEquiv_top_bottom_naturality adj₀ adj₂ α
    (TwoSquare.hComp α₁ α₂) γ δ hα K
  rw [mateEquiv_hComp_app adj₀ adj₁ adj₂] at hm
  exact hm

end CategoryTheory
