/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MateHomEquiv
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Original composite adjunction mates on Hom sets

The original image unit and right-adjoint comparison retain their exact maps.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}

/-- The native composite comparison transposes to the original unit followed by the
right-adjoint comparison, for every original coefficient arrow. -/
theorem homEquiv_leftAdjointCompIso_inv_map
    (a₀₁ : F₀₁ ⊣ G₁₀) (a₁₂ : F₁₂ ⊣ G₂₁) (a₀₂ : F₀₂ ⊣ G₂₀)
    (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) {A : C₀} {B : C₁} (f : F₀₁.obj A ⟶ B) :
    a₀₂.homEquiv A (F₁₂.obj B)
        ((leftAdjointCompIso a₀₁ a₁₂ a₀₂ e).inv.app A ≫ F₁₂.map f) =
      a₀₁.homEquiv A B f ≫ G₁₀.map (a₁₂.unit.app B) ≫ e.hom.app (F₁₂.obj B) := by
  have hmap : a₁₂.homEquiv _ _ (F₁₂.map f) = f ≫ a₁₂.unit.app B := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      a₁₂.homEquiv_naturality_left f (𝟙 (F₁₂.obj B))
  calc
    _ = (a₀₁.comp a₁₂).homEquiv A (F₁₂.obj B) (F₁₂.map f) ≫
        e.hom.app (F₁₂.obj B) := by
      simpa only [conjugateEquiv_leftAdjointCompIso_inv] using
        (CategoryTheory.homEquiv_conjugate (a₀₁.comp a₁₂) a₀₂
          (leftAdjointCompIso a₀₁ a₁₂ a₀₂ e).inv (F₁₂.map f))
    _ = a₀₁.homEquiv A _ (f ≫ a₁₂.unit.app B) ≫ e.hom.app (F₁₂.obj B) := by
      rw [comp_homEquiv, Equiv.trans_apply, hmap]
      rfl
    _ = _ := by rw [a₀₁.homEquiv_naturality_right, Category.assoc]

end CategoryTheory.Adjunction
