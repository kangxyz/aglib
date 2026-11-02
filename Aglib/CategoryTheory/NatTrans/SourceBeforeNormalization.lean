/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA₁ uA₂ uE uE' vA vA₁ vA₂ vE vE'

/-- Naturality of the original target normalization transports the whole equation. -/
theorem sourceIsoBeforeExchange_normalize
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ : A₁ ⥤ E} {F₂ N₂ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s : F ≅ V₁ ⋙ F₁) (β₁ : F₁ ⋙ B ⟶ V₂ ⋙ F₂)
    (β : F ⋙ B ⟶ V ⋙ F₂) (c : V ≅ V₁ ⋙ V₂) (n : F₂ ⟶ N₂)
    (β₁N : F₁ ⋙ B ⟶ V₂ ⋙ N₂) (βN : F ⋙ B ⟶ V ⋙ N₂)
    (h : SourceIsoBeforeExchangeEquation s β₁ β c)
    (h₁ : β₁N = β₁ ≫ Functor.whiskerLeft V₂ n)
    (hN : βN = β ≫ Functor.whiskerLeft V n) :
    SourceIsoBeforeExchangeEquation s β₁N βN c := by
  intro K
  have hn := n.naturality (c.hom.app K)
  simp only [h₁, hN, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  have hh := congrArg (fun z => z ≫ n.app (V₂.obj (V₁.obj K))) (h K)
  simp only [Category.assoc] at hh
  dsimp only [Functor.comp_obj] at hn
  exact hh.trans (congrArg (fun z => β.app K ≫ z) hn)

end CategoryTheory
