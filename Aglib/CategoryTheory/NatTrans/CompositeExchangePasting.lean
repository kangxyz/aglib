/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchange

/-!
# Consecutive pasting for the original composite exchange

The two hypotheses are the original right-exchange and left-comparison pasting
squares. This lemma combines them without changing any comparison or imposing
invertibility on the right exchange. Concrete geometric consumers must supply
both squares; this is not itself a base-change coherence theorem.
-/

@[expose] public section

namespace CategoryTheory

universe uA₀ uB₀ uC₀ uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ vA₀ vB₀ vC₀ vA₁ vB₁ vC₁ vA₂ vB₂ vC₂


variable {A₀ : Type uA₀} {B₀ : Type uB₀} {C₀ : Type uC₀} {A₁ : Type uA₁} {B₁ : Type uB₁}
  {C₁ : Type uC₁} {A₂ : Type uA₂} {B₂ : Type uB₂} {C₂ : Type uC₂}
  [Category.{vA₀} A₀] [Category.{vB₀} B₀] [Category.{vC₀} C₀]
  [Category.{vA₁} A₁] [Category.{vB₁} B₁] [Category.{vC₁} C₁]
  [Category.{vA₂} A₂] [Category.{vB₂} B₂] [Category.{vC₂} C₂]
  {J₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ C₀}
  {J₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ C₁}
  {J₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ C₂}
  {F₁ : A₀ ⥤ A₁} {H₁ : B₀ ⥤ B₁} {G₁ : C₀ ⥤ C₁}
  {F₂ : A₁ ⥤ A₂} {H₂ : B₁ ⥤ B₂} {G₂ : C₁ ⥤ C₂}
  {F₀₂ : A₀ ⥤ A₂} {H₀₂ : B₀ ⥤ B₂} {G₀₂ : C₀ ⥤ C₂}

/-- Pasting of the original right and left comparisons gives the corresponding
pasting of their composite exchanges, retaining the three specified compositors. -/
theorem compositeExchange_pasting_app
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β₀₂ : R₀ ⋙ G₀₂ ⟶ H₀₂ ⋙ R₂)
    (e₁ : J₀ ⋙ H₁ ≅ F₁ ⋙ J₁) (e₂ : J₁ ⋙ H₂ ≅ F₂ ⋙ J₂)
    (e₀₂ : J₀ ⋙ H₀₂ ≅ F₀₂ ⋙ J₂)
    (γ : G₀₂ ⟶ G₁ ⋙ G₂) (η : H₀₂ ⟶ H₁ ⋙ H₂) (φ : F₀₂ ⟶ F₁ ⋙ F₂)
    (K : A₀)
    (hβ : γ.app (R₀.obj (J₀.obj K)) ≫
        G₂.map (β₁.app (J₀.obj K)) ≫ β₂.app (H₁.obj (J₀.obj K)) =
      β₀₂.app (J₀.obj K) ≫ R₂.map (η.app (J₀.obj K)))
    (he : η.app (J₀.obj K) ≫ H₂.map (e₁.hom.app K) ≫
        e₂.hom.app (F₁.obj K) = e₀₂.hom.app K ≫ J₂.map (φ.app K)) :
    γ.app ((J₀ ⋙ R₀).obj K) ≫ G₂.map ((compositeExchange β₁ e₁).app K) ≫
        (compositeExchange β₂ e₂).app (F₁.obj K) =
      (compositeExchange β₀₂ e₀₂).app K ≫ (J₂ ⋙ R₂).map (φ.app K) := by
  have hn : G₂.map (R₁.map (e₁.hom.app K)) ≫ β₂.app (J₁.obj (F₁.obj K)) =
      β₂.app (H₁.obj (J₀.obj K)) ≫ R₂.map (H₂.map (e₁.hom.app K)) :=
    β₂.naturality (e₁.hom.app K)
  simp only [compositeExchange_app, Functor.map_comp, Functor.comp_obj, Functor.comp_map]
  calc
    _ = (γ.app (R₀.obj (J₀.obj K)) ≫ G₂.map (β₁.app (J₀.obj K)) ≫
        β₂.app (H₁.obj (J₀.obj K))) ≫
        R₂.map (H₂.map (e₁.hom.app K)) ≫ R₂.map (e₂.hom.app (F₁.obj K)) := by
      simp only [Category.assoc]
      rw [← Category.assoc (G₂.map (R₁.map (e₁.hom.app K))), hn]
      simp only [Category.assoc]
    _ = β₀₂.app (J₀.obj K) ≫
        R₂.map (η.app (J₀.obj K) ≫ H₂.map (e₁.hom.app K) ≫
          e₂.hom.app (F₁.obj K)) := by
      rw [hβ]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [he]
      simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
