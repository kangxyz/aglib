/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA₁ uA₂ uE uE' vA vA₁ vA₂ vE vE'

/-- Change the source-transported intermediate model through its original refinement
and the proved original exchange square, without identifying the models. -/
theorem sourceIsoBeforeExchange_changeModel
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ G₁ : A₁ ⥤ E} {F₂ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s : F ≅ V₁ ⋙ F₁) (s' : F ≅ V₁ ⋙ G₁) (m : F₁ ⟶ G₁)
    (β₁ : F₁ ⋙ B ⟶ V₂ ⋙ F₂) (β₁' : G₁ ⋙ B ⟶ V₂ ⋙ F₂)
    (β : F ⋙ B ⟶ V ⋙ F₂) (c : V ≅ V₁ ⋙ V₂) (t : F₂ ⟶ F₂)
    (h : SourceIsoBeforeExchangeEquation s β₁ β c)
    (hs : s'.hom = s.hom ≫ Functor.whiskerLeft V₁ m)
    (hn : ExchangeNaturalityEquation m β₁' β₁ t) (ht : t = 𝟙 F₂) :
    SourceIsoBeforeExchangeEquation s' β₁' β c := by
  subst t
  intro K
  have hnK := congrArg (fun z => z.app (V₁.obj K)) hn
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app, Functor.comp_obj] at hnK
  simp only [Category.comp_id] at hnK
  simp only [hs, NatTrans.comp_app, Functor.whiskerLeft_app, B.map_comp, Category.assoc]
  rw [hnK]
  exact h K

end CategoryTheory
