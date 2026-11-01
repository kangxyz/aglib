/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MatePastingReflection
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SquarePasting

/-! # Pasting reflection with identified original mates

Keep the original right squares and their whole mate-identification equations
as parameters. Concrete consumers need not normalize evaluated mate expressions.
-/

@[expose] public section

universe uA vA uB vB uC vC uD vD
universe uE vE uF vF

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE}
  {F : Type uF}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    [Category.{vF} F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A} {L₀' : D ⥤ F} {R₀' : F ⥤ D}

/-- Reflect proved horizontal pasting of the identified original right squares
through their actual adjunction mates and conjugate compositors. -/
theorem verticalSquareEquation_of_identified_mates
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    (γ : TwoSquare G L₀ L₀' K)
    (c₁ : L₀ ≅ L₁ ⋙ L₃) (c₂ : L₀' ≅ L₂ ⋙ L₄)
    (d₁ : R₀ ≅ R₃ ⋙ R₁) (d₂ : R₀' ≅ R₄ ⋙ R₂)
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (a₀ : L₀ ⊣ R₀) (a₀' : L₀' ⊣ R₀')
    (hc₁ : conjugateEquiv (a₁.comp a₃) a₀ c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv (a₂.comp a₄) a₀' c₂.hom = d₂.inv)
    (τ₁ : TwoSquare R₁ H G R₂) (τ₂ : TwoSquare R₃ K H R₄)
    (τ : TwoSquare R₀ K G R₀')
    (h₁ : mateEquiv a₁ a₂ α = τ₁) (h₂ : mateEquiv a₃ a₄ β = τ₂)
    (h₀ : mateEquiv a₀ a₀' γ = τ)
    (hp : ∀ M, HorizontalSquareEquation τ₂ τ₁ τ d₁.hom d₂.hom M)
    (X : A) : VerticalSquareEquation α β γ c₁ c₂ X := by
  apply verticalSquareEquation_of_mates α β γ c₁ c₂ d₁ d₂
    a₁ a₂ a₃ a₄ a₀ a₀' hc₁ hc₂ _ X
  intro M
  simpa only [VerticalMateEquation, h₁, h₂, h₀, HorizontalSquareEquation] using hp M

/-- Complete inversion of original square pasting, before any native specialization. -/
theorem forward_horizontal_of_inverse_vertical
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE}
  {F : Type uF}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
      [Category.{vF} F]
    {J₁ : B ⥤ A} {J₂ : C ⥤ B} {I₁ : E ⥤ D} {I₂ : F ⥤ E}
    {P₀ : A ⥤ D} {P₁ : B ⥤ E} {P₂ : C ⥤ F} {J : C ⥤ A} {I : F ⥤ D}
    (e₁ : J₁ ⋙ P₀ ≅ P₁ ⋙ I₁) (e₂ : J₂ ⋙ P₁ ≅ P₂ ⋙ I₂)
    (e : J ⋙ P₀ ≅ P₂ ⋙ I) (cJ : J ≅ J₂ ⋙ J₁) (cI : I ≅ I₂ ⋙ I₁)
    (h : ∀ K, VerticalSquareEquation
      (TwoSquare.mk _ _ _ _ e₂.inv) (TwoSquare.mk _ _ _ _ e₁.inv)
      (TwoSquare.mk _ _ _ _ e.inv) cJ cI K) (K : C) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ e₂.hom) (TwoSquare.mk _ _ _ _ e₁.hom)
      (TwoSquare.mk _ _ _ _ e.hom) cJ.hom cI.hom K := by
  have hh := congrArg (fun a => e.hom.app K ≫ a ≫ e₁.hom.app (J₂.obj K) ≫
    I₁.map (e₂.hom.app K)) (h K)
  dsimp only [VerticalSquareEquation, HorizontalSquareEquation, TwoSquare.mk,
    TwoSquare.natTrans, Functor.comp_obj] at hh ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← I₁.map_comp, Iso.inv_hom_id_app] at hh
  rw [I₁.map_id ((P₂ ⋙ I₂).obj K)] at hh
  change e.hom.app K ≫ cI.hom.app (P₂.obj K) ≫
      𝟙 ((I₂ ⋙ I₁).obj (P₂.obj K)) = _ at hh
  rw [Category.comp_id (cI.hom.app (P₂.obj K))] at hh
  exact hh.symm


/-- The reverse whole normalization: original horizontal pasting gives vertical
pasting of the inverse original square isomorphisms. -/
theorem inverse_vertical_of_forward_horizontal
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE}
  {F : Type uF}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
      [Category.{vF} F]
    {J₁ : B ⥤ A} {J₂ : C ⥤ B} {I₁ : E ⥤ D} {I₂ : F ⥤ E}
    {P₀ : A ⥤ D} {P₁ : B ⥤ E} {P₂ : C ⥤ F} {J : C ⥤ A} {I : F ⥤ D}
    (e₁ : J₁ ⋙ P₀ ≅ P₁ ⋙ I₁) (e₂ : J₂ ⋙ P₁ ≅ P₂ ⋙ I₂)
    (e : J ⋙ P₀ ≅ P₂ ⋙ I) (cJ : J ≅ J₂ ⋙ J₁) (cI : I ≅ I₂ ⋙ I₁)
    (h : ∀ K, HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ e₂.hom) (TwoSquare.mk _ _ _ _ e₁.hom)
      (TwoSquare.mk _ _ _ _ e.hom) cJ.hom cI.hom K) (K : C) :
    VerticalSquareEquation
      (TwoSquare.mk _ _ _ _ e₂.inv) (TwoSquare.mk _ _ _ _ e₁.inv)
      (TwoSquare.mk _ _ _ _ e.inv) cJ cI K := by
  have hh := congrArg (fun z => e.inv.app K ≫ z ≫
    I₁.map (e₂.inv.app K) ≫ e₁.inv.app (J₂.obj K)) (h K)
  dsimp only [HorizontalSquareEquation, VerticalSquareEquation, TwoSquare.mk,
    TwoSquare.natTrans, Functor.comp_obj] at hh ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← I₁.map_comp_assoc,
    Iso.hom_inv_id_app] at hh
  rw [I₁.map_id ((J₂ ⋙ P₁).obj K)] at hh
  dsimp only [Functor.comp_obj] at hh
  simp only [Category.id_comp, Iso.hom_inv_id_app] at hh
  change e.inv.app K ≫ P₀.map (cJ.hom.app K) ≫
      𝟙 (P₀.obj ((J₂ ⋙ J₁).obj K)) = _ at hh
  rw [Category.comp_id (P₀.map (cJ.hom.app K))] at hh
  exact hh.symm

end CategoryTheory
