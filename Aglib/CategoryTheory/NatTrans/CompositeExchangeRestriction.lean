/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchange

/-!
# Source restriction of exchange naturality

A specified comparison of source inclusions transports the original exchange
naturality square. All associators remain those of `compositeExchange`.
-/

@[expose] public section

namespace CategoryTheory

universe uP uA uB uA' uB' uP' vP vA vB vA' vB' vP'


variable {P : Type uP} {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'} {P' : Type uP'}
  [Category.{vP} P] [Category.{vA} A] [Category.{vB} B]
  [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vP'} P']
  {K : P ⥤ A} {K' : P' ⥤ A'} {V : P ⥤ P'} {a : A ⥤ A'} {G : B ⥤ B'}
  {F₁ F₂ : A ⥤ B} {F₁' F₂' : A' ⥤ B'}

/-- Naturality of the original exchange survives the specified source
restriction and the original comparison of source inclusions. -/
theorem compositeExchange_restriction_naturality
    (β₁ : F₁ ⋙ G ⟶ a ⋙ F₁') (β₂ : F₂ ⋙ G ⟶ a ⋙ F₂')
    (e : K ⋙ a ≅ V ⋙ K') (δ : F₂ ⟶ F₁) (δ' : F₂' ⟶ F₁')
    (h : Functor.whiskerRight δ G ≫ β₁ = β₂ ≫ Functor.whiskerLeft a δ') :
    Functor.whiskerRight (Functor.whiskerLeft K δ) G ≫ compositeExchange β₁ e =
      compositeExchange β₂ e ≫ Functor.whiskerLeft V (Functor.whiskerLeft K' δ') := by
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun t => t.app (K.obj x)) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hx
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    compositeExchange_app]
  rw [← Category.assoc, hx, Category.assoc]
  simpa only [Functor.comp_obj, Category.assoc] using
    congrArg (fun t => β₂.app (K.obj x) ≫ t) (δ'.naturality (e.hom.app x)).symm

end CategoryTheory
