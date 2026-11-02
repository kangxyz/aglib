/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.CategoryTheory.NatTrans.SourceIsoComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA₁ uA₂ uE vA vA₁ vA₂ vE

/-- Mixed identity refinements are moved through the original source transport using
its proved naturality; no equality of independent derived models is used. -/
theorem sourceIsoComposition_changeMiddleModels
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E]
    {F : A ⥤ E} {F₁ G₁ : A₁ ⥤ E} {F₂ G₂ H₂ F₂' : A₂ ⥤ E}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s₁ : F ≅ V₁ ⋙ F₁) (s₂ : F₁ ≅ V₂ ⋙ F₂)
    (s : F ≅ V ⋙ F₂') (t : F₂' ⟶ F₂) (c : V ≅ V₁ ⋙ V₂)
    (m₁ : F₁ ⟶ G₁) (m₂ : F₂ ⟶ G₂) (n₂ : G₂ ⟶ H₂)
    (s₂' : G₁ ≅ V₂ ⋙ G₂) (s₁' : F ≅ V₁ ⋙ G₁) (s₂'' : G₁ ≅ V₂ ⋙ H₂)
    (t' : F₂' ⟶ H₂)
    (h : SourceIsoCompositionEquation s₁ s₂ s t c)
    (hn : SourceIsoNaturalityEquation m₁ m₂ s₂' s₂)
    (h₁ : s₁'.hom = s₁.hom ≫ Functor.whiskerLeft V₁ m₁)
    (h₂ : s₂''.hom = s₂'.hom ≫ Functor.whiskerLeft V₂ n₂)
    (ht : t' = t ≫ m₂ ≫ n₂) :
    SourceIsoCompositionEquation s₁' s₂'' s t' c := by
  intro K
  have hnK := congrArg (fun z => z.app (V₁.obj K)) hn
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hnK
  have hc := (m₂ ≫ n₂).naturality (c.hom.app K)
  simp only [NatTrans.comp_app] at hc
  simp only [ht, h₁, h₂, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← Category.assoc (m₂.app (V.obj K)), ← hc]
  have hr :
      s.hom.app K ≫ t.app (V.obj K) ≫ F₂.map (c.hom.app K) ≫
          m₂.app ((V₁ ⋙ V₂).obj K) ≫ n₂.app ((V₁ ⋙ V₂).obj K) =
        s₁.hom.app K ≫ s₂.hom.app (V₁.obj K) ≫
          m₂.app ((V₁ ⋙ V₂).obj K) ≫ n₂.app ((V₁ ⋙ V₂).obj K) := by
    simpa only [Category.assoc] using congrArg
      (fun z => z ≫ m₂.app ((V₁ ⋙ V₂).obj K) ≫ n₂.app ((V₁ ⋙ V₂).obj K)) (h K)
  apply hr.trans
  simpa only [Category.assoc, Functor.comp_obj] using congrArg
    (fun z => s₁.hom.app K ≫ z ≫ n₂.app (V₂.obj (V₁.obj K))) hnK.symm

end CategoryTheory
