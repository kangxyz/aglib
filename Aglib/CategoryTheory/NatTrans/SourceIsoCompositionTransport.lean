/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceIsoComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA₁ uA₂ uE vA vA₁ vA₂ vE

/-- Absorb an original target refinement into its actual canonical source comparison. -/
theorem sourceIsoComposition_absorbTarget
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E]
    {F : A ⥤ E} {F₁ : A₁ ⥤ E} {F₂ F₂' : A₂ ⥤ E}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s₁ : F ≅ V₁ ⋙ F₁) (s₂ : F₁ ≅ V₂ ⋙ F₂)
    (s : F ≅ V ⋙ F₂') (t : F₂' ⟶ F₂) (c : V ≅ V₁ ⋙ V₂)
    (s' : F ≅ V ⋙ F₂) (hs : s'.hom = s.hom ≫ Functor.whiskerLeft V t)
    (h : SourceIsoCompositionEquation s₁ s₂ s t c) :
    SourceIsoCompositionEquation s₁ s₂ s' (𝟙 F₂) c := by
  intro K
  simpa only [hs, NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app,
    Functor.comp_obj, Category.id_comp, Category.assoc] using h K

/-- Canonical model squares transport the whole composition equation; no chosen
isomorphism or equality of models is substituted for the original maps. -/
theorem sourceIsoComposition_modelTransport
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E]
    {F G : A ⥤ E} {F₁ G₁ : A₁ ⥤ E} {F₂ G₂ : A₂ ⥤ E}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s₁ : F ≅ V₁ ⋙ F₁) (s₂ : F₁ ≅ V₂ ⋙ F₂) (s : F ≅ V ⋙ F₂)
    (t₁ : G ≅ V₁ ⋙ G₁) (t₂ : G₁ ≅ V₂ ⋙ G₂) (t : G ≅ V ⋙ G₂)
    (c : V ≅ V₁ ⋙ V₂) (a : F ≅ G) (a₁ : F₁ ≅ G₁) (a₂ : F₂ ≅ G₂)
    (h₁ : a ≪≫ t₁ = s₁ ≪≫ Functor.isoWhiskerLeft V₁ a₁)
    (h₂ : a₁ ≪≫ t₂ = s₂ ≪≫ Functor.isoWhiskerLeft V₂ a₂)
    (hs : a ≪≫ t = s ≪≫ Functor.isoWhiskerLeft V a₂)
    (h : SourceIsoCompositionEquation t₁ t₂ t (𝟙 G₂) c) :
    SourceIsoCompositionEquation s₁ s₂ s (𝟙 F₂) c := by
  intro K
  have h₁K := congrArg (fun z => z.hom.app K) h₁
  have h₂K := congrArg (fun z => z.hom.app (V₁.obj K)) h₂
  have hsK := congrArg (fun z => z.hom.app K) hs
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app] at h₁K h₂K hsK
  have hK := h K
  dsimp only [NatTrans.id_app, Functor.comp_obj] at hK ⊢
  simp only [Category.id_comp] at hK ⊢
  apply (cancel_mono (a₂.hom.app ((V₁ ⋙ V₂).obj K))).mp
  calc
    (s.hom.app K ≫ F₂.map (c.hom.app K)) ≫ _ =
        (s.hom.app K ≫ a₂.hom.app (V.obj K)) ≫ G₂.map (c.hom.app K) := by
      rw [Category.assoc, a₂.hom.naturality, ← Category.assoc]
    _ = (a.hom.app K ≫ t.hom.app K) ≫ G₂.map (c.hom.app K) := by rw [hsK]
    _ = (a.hom.app K ≫ t₁.hom.app K) ≫ t₂.hom.app (V₁.obj K) := by
      rw [Category.assoc, hK, ← Category.assoc]
    _ = (s₁.hom.app K ≫ s₂.hom.app (V₁.obj K)) ≫ _ := by
      rw [h₁K, Category.assoc, h₂K, ← Category.assoc]
      rfl

end CategoryTheory
