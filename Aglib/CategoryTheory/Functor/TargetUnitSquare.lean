/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Target transport of original unit-normalized squares -/

@[expose] public noncomputable section
namespace CategoryTheory
variable {A B T₀ T₁ : Type*}
  [Category* A] [Category* B] [Category* T₀] [Category* T₁]
  (G₀ : A ⥤ T₀) (G₁ : A ⥤ T₁) (R₀ : B ⥤ T₀) (R₁ : B ⥤ T₁)
  (E : T₀ ⥤ T₁) (s : G₀ ⋙ E ≅ G₁) (t : R₀ ⋙ E ≅ R₁)
  {a a' : A} {b b' : B} (α : a ⟶ a') (δ : b ≅ b')
  (β₀ : G₀.obj a' ⟶ R₀.obj b) (β₁ : G₁.obj a' ⟶ R₁.obj b)
  {W₀ : T₀} {W₁ : T₁} (g₀ : G₀.obj a ⟶ W₀) (g₁ : G₁.obj a ⟶ W₁)
  (q : E.obj W₀ ⟶ W₁) (θ₀ : W₀ ⟶ R₀.obj b') (θ₁ : W₁ ⟶ R₁.obj b')

/-- Coherence of the original units implies the target square after precomposition
by that same unit. No nonexact unit is cancelled. -/
theorem targetUnitSquare
    (h₀ : G₀.map α ≫ β₀ ≫ R₀.map δ.hom = g₀ ≫ θ₀)
    (h₁ : G₁.map α ≫ β₁ ≫ R₁.map δ.hom = g₁ ≫ θ₁)
    (hg : E.map g₀ ≫ q = s.hom.app a ≫ g₁)
    (hθ : E.map θ₀ ≫ t.hom.app b' = q ≫ θ₁) :
    E.map (G₀.map α) ≫ E.map β₀ ≫ t.hom.app b =
      E.map (G₀.map α) ≫ s.hom.app a' ≫ β₁ := by
  apply (cancel_mono (R₁.map δ.hom)).mp
  simp only [Category.assoc]
  rw [← t.hom.naturality δ.hom]
  simp only [Functor.comp_map]
  rw [← Category.assoc (E.map β₀), ← E.map_comp,
    ← Category.assoc (E.map (G₀.map α)), ← E.map_comp, h₀, E.map_comp,
    Category.assoc, hθ, ← Category.assoc, hg, Category.assoc, ← h₁]
  simp only [← Category.assoc]
  rw [← s.hom.naturality α]
  rfl

end CategoryTheory
