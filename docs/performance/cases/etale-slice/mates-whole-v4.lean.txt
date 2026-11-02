/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Component normalization of the canonical base-change mate

The map is Mathlib's original `mateEquiv`, not a second exchange construction.
The equations here expose its component formula, uniqueness, identity normalization
and the two pasting formulas used by bounded-below derived direct images.
The adjunctions are parameters: this file does not construct derived adjunctions
or assert that an exchange map is invertible.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open Category CategoryTheory.Functor TwoSquare

section Components

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F}
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The canonical exchange component is the target unit, the square, and the source counit. -/
@[reassoc]
theorem mateEquiv_app_eq (α : TwoSquare G L₁ L₂ H) (K : D) :
    (mateEquiv adj₁ adj₂ α).app K =
      adj₂.unit.app (G.obj (R₁.obj K)) ≫
        R₂.map (α.app (R₁.obj K)) ≫ R₂.map (H.map (adj₁.counit.app K)) := by
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    rightUnitor_inv_app, CategoryTheory.Functor.whiskerLeft_app, associator_hom_app,
    associator_inv_app, CategoryTheory.Functor.whiskerRight_app, leftUnitor_hom_app,
    comp_obj, CategoryTheory.Functor.comp_map, Category.id_comp]
  change adj₂.unit.app (G.obj (R₁.obj K)) ≫
      (R₂.map (α.app (R₁.obj K)) ≫
        (R₂.map (H.map (adj₁.counit.app K)) ≫ 𝟙 _)) = _
  rw [Category.comp_id]

/-- The counit equation determines the exchange transformation uniquely. -/
theorem eq_mateEquiv_iff (α : TwoSquare G L₁ L₂ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂) :
    β = (mateEquiv adj₁ adj₂ α).natTrans ↔
      ∀ K : D, L₂.map (β.app K) ≫ adj₂.counit.app (H.obj K) =
        α.app (R₁.obj K) ≫ H.map (adj₁.counit.app K) := by
  constructor
  · rintro rfl K
    exact mateEquiv_counit adj₁ adj₂ α K
  · intro h
    ext K
    apply (adj₂.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    exact (h K).trans (mateEquiv_counit adj₁ adj₂ α K).symm

end Components

section Identity

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

-- These public identities are explicit rewrite rules.
-- Mathlib's mate formula owns the simp normal form.
/-- Identity base change has the vertical identity square as its canonical mate. -/
theorem mateEquiv_hId : mateEquiv adj adj (TwoSquare.hId L) = TwoSquare.vId R := by
  ext K
  rw [mateEquiv_app_eq]
  simp [TwoSquare.hId, TwoSquare.vId, adj.right_triangle_components]

/-- Identity vertical morphisms have the horizontal identity square as their mate. -/
theorem mateEquiv_vId (G : C ⥤ D) :
    mateEquiv Adjunction.id Adjunction.id (TwoSquare.vId G) = TwoSquare.hId G := by
  ext K
  rw [mateEquiv_app_eq]
  simp [TwoSquare.hId, TwoSquare.vId, Adjunction.id]

end Identity

section HorizontalBaseChange

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  [Category.{v₅} E] [Category.{v₆} F]
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₃ : E ⥤ F} {R₃ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- For successive base changes, first pull back the first exchange, then use the second.
The original `TwoSquare` composition retains all associators. -/
@[reassoc]
theorem mateEquiv_hComp_app (α : TwoSquare G₁ L₁ L₂ H₁)
    (β : TwoSquare G₂ L₂ L₃ H₂) (K : B) :
    (mateEquiv adj₁ adj₃ (α ≫ₕ β)).app K =
      G₂.map ((mateEquiv adj₁ adj₂ α).app K) ≫
        (mateEquiv adj₂ adj₃ β).app (H₁.obj K) := by
  rw [mateEquiv_vcomp adj₁ adj₂ adj₃]
  simp [TwoSquare.vComp]

end HorizontalBaseChange

section VerticalBaseChange

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  [Category.{v₅} E] [Category.{v₆} F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)

/-- For composed vertical morphisms, use the first exchange at the inner direct image,
then apply the outer direct image to the second exchange. -/
@[reassoc]
theorem mateEquiv_vComp_app (α : TwoSquare G L₁ L₂ H)
    (β : TwoSquare H L₃ L₄ K) (M : C) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄) (α ≫ᵥ β)).app M =
      (mateEquiv adj₁ adj₂ α).app (R₃.obj M) ≫
        R₂.map ((mateEquiv adj₃ adj₄ β).app M) := by
  rw [mateEquiv_hcomp adj₁ adj₂ adj₃ adj₄]
  simp [TwoSquare.hComp]

end VerticalBaseChange

end CategoryTheory
