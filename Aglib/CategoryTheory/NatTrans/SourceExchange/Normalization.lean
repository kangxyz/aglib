/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uB uA' uB' vA vB vA' vB'

theorem append_original_normalization
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'} [Category.{vA} A]
    [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    {F₁ F₂ : A ⥤ B} {G : B ⥤ B'} {V : A ⥤ A'} {R₁ R₂ N : A' ⥤ B'}
    (δ : F₂ ⟶ F₁) (β₁ : F₁ ⋙ G ⟶ V ⋙ R₁) (β₂ : F₂ ⋙ G ⟶ V ⋙ R₂)
    (δ' : R₂ ⟶ R₁) (n : R₁ ⟶ N) (βN : F₁ ⋙ G ⟶ V ⋙ N)
    (h : ExchangeNaturalityEquation δ β₁ β₂ δ')
    (hn : βN = β₁ ≫ Functor.whiskerLeft V n) :
    ExchangeNaturalityEquation δ βN β₂ (δ' ≫ n) := by
  change Functor.whiskerRight δ G ≫ βN = β₂ ≫ Functor.whiskerLeft V (δ' ≫ n)
  rw [hn, ← Category.assoc, h, Category.assoc, Functor.whiskerLeft_comp]

end CategoryTheory
