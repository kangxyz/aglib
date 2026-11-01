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

/-- Whole source-pasting equation retaining the specified original target transition. -/
def RefinedSourceIsoPastingEquation
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ : A₁ ⥤ E'} {F₂ F₃ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (β : F ⋙ B ⟶ V₁ ⋙ F₁) (β' : F ⋙ B ⟶ V ⋙ F₃)
    (c : V ≅ V₁ ⋙ V₂) (s : F₁ ≅ V₂ ⋙ F₂) (t : F₂ ⟶ F₃) : Prop :=
  ∀ K, β'.app K ≫ F₃.map (c.hom.app K) =
    β.app K ≫ s.hom.app (V₁.obj K) ≫ t.app ((V₁ ⋙ V₂).obj K)

/-- Assemble the original target-refinement law, actual source-arrow transport,
and source-only pasting. No invertibility of the target transition is used. -/
theorem refinedSourceIsoPasting_of_equations
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ : A₁ ⥤ E'} {F₂ F₃ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V V' : A ⥤ A₂}
    (β : F ⋙ B ⟶ V₁ ⋙ F₁) (β' : F ⋙ B ⟶ V' ⋙ F₂)
    (β₀ : F ⋙ B ⟶ V ⋙ F₂) (β₃ : F ⋙ B ⟶ V ⋙ F₃)
    (d : V ≅ V') (c : V' ≅ V₁ ⋙ V₂) (s : F₁ ≅ V₂ ⋙ F₂) (t : F₂ ⟶ F₃)
    (ht : TargetIsoBaseChangeEquation β₃ β₀ t)
    (hd : β₀ ≫ Functor.whiskerRight d.hom F₂ = β')
    (hs : CompactifiedSourceIsoPastingEquation β β' c s) :
    RefinedSourceIsoPastingEquation β β₃ (d ≪≫ c) s t := by
  intro K
  have htK := congrArg (fun z => z.app K) ht
  have hdK := congrArg (fun z => z.app K) hd
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at htK
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hdK
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp]
  rw [htK]
  simp only [Category.assoc]
  rw [← t.naturality_assoc (d.hom.app K), ← Category.assoc, hdK,
    ← t.naturality (c.hom.app K), ← Category.assoc, hs K, Category.assoc]

end CategoryTheory
