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

universe uA uA₁ uA₂ uE vA vA₁ vA₂ vE

/-- Whole source-composition equation, retaining the supplied original target comparison. -/
def SourceIsoCompositionEquation
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E]
    {F : A ⥤ E} {F₁ : A₁ ⥤ E} {F₂ F₂' : A₂ ⥤ E}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s₁ : F ≅ V₁ ⋙ F₁) (s₂ : F₁ ≅ V₂ ⋙ F₂)
    (s : F ≅ V ⋙ F₂') (t : F₂' ⟶ F₂) (c : V ≅ V₁ ⋙ V₂) : Prop :=
  ∀ K, s.hom.app K ≫ t.app (V.obj K) ≫ F₂.map (c.hom.app K) =
    s₁.hom.app K ≫ s₂.hom.app (V₁.obj K)

/-- Base identity cancellation is performed abstractly before any native derived models
are substituted. Both exchange equations and the pasted exchange remain the originals. -/
theorem sourceIsoComposition_of_exchange
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E]
    {F : A ⥤ E} {F₁ : A₁ ⥤ E} {F₂ F₂' : A₂ ⥤ E}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂} {I : E ⥤ E}
    (β₁ : F ⋙ I ⟶ V₁ ⋙ F₁) (β : F ⋙ I ⟶ V ⋙ F₂')
    (s₁ : F ≅ V₁ ⋙ F₁) (s₂ : F₁ ≅ V₂ ⋙ F₂)
    (s : F ≅ V ⋙ F₂') (t : F₂' ⟶ F₂) (c : V ≅ V₁ ⋙ V₂)
    (d : I ≅ 𝟭 E)
    (h₁ : SourceIsoExchangeEquation β₁ d s₁)
    (h : SourceIsoExchangeEquation β d s)
    (hp : CompactifiedSourceIsoPastingEquation β₁
      (β ≫ Functor.whiskerLeft V t) c s₂) :
    SourceIsoCompositionEquation s₁ s₂ s t c := by
  intro K
  have hk := hp K
  change (β.app K ≫ t.app (V.obj K)) ≫ F₂.map (c.hom.app K) =
    β₁.app K ≫ s₂.hom.app (V₁.obj K) at hk
  rw [h K, h₁ K] at hk
  exact (cancel_epi (d.hom.app (F.obj K))).mp (by simpa only [Category.assoc] using hk)

end CategoryTheory
