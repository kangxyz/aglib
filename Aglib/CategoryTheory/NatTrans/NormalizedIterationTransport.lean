/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.ExchangePastingTransport
public import Aglib.CategoryTheory.NatTrans.NormalizedIteration
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA₁ uA₂ uAs uB uB₁ uB₂ vA vA₁ vA₂ vAs vB vB₁ vB₂

variable {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {As : Type uAs} {B : Type uB}
  {B₁ : Type uB₁} {B₂ : Type uB₂}
  [Category.{vA} A] [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vAs} As]
  [Category.{vB} B] [Category.{vB₁} B₁] [Category.{vB₂} B₂]
  {F M : A ⥤ B} {F₁ M₁ : A₁ ⥤ B₁} {F₂ M₂ Mt : A₂ ⥤ B₂}
  {Fs Ms : As ⥤ B₂}
  {G₁ : B ⥤ B₁} {G₂ : B₁ ⥤ B₂} {G : B ⥤ B₂}
  {H₁ : A ⥤ A₁} {H₂ : A₁ ⥤ A₂} {H : A ⥤ A₂} {V : A ⥤ As} {E : As ⥤ A₂}

/-- All three exchange squares and the source/refinement square concern the
specified original maps. Thus no total exchange or geometric law is assumed. -/
theorem originalNormalizedIterationEquation_transport
    (c : F ≅ M) (c₁ : F₁ ≅ M₁) (c₂ : F₂ ≅ M₂) (cs : Fs ≅ Ms)
    (β₁ : F ⋙ G₁ ⟶ H₁ ⋙ F₁) (β₂ : F₁ ⋙ G₂ ⟶ H₂ ⋙ F₂)
    (βs : F ⋙ G ⟶ V ⋙ Fs)
    (μ₁ : M ⋙ G₁ ⟶ H₁ ⋙ M₁) (μ₂ : M₁ ⋙ G₂ ⟶ H₂ ⋙ M₂)
    (μs : M ⋙ G ⟶ V ⋙ Ms)
    (γ : G ≅ G₁ ⋙ G₂) (δ : H ≅ H₁ ⋙ H₂) (η : H ≅ V ⋙ E)
    (ψ : Fs ≅ E ⋙ F₂) (s : Ms ≅ E ⋙ Mt) (t : Mt ⟶ M₂)
    (h₁ : ExchangeModelComparisonEquation c c₁ β₁ μ₁)
    (h₂ : ExchangeModelComparisonEquation c₁ c₂ β₂ μ₂)
    (hs : ExchangeModelComparisonEquation c cs βs μs)
    (hψ : cs.hom ≫ s.hom ≫ Functor.whiskerLeft E t =
      ψ.hom ≫ Functor.whiskerLeft E c₂.hom)
    (hm : OriginalNormalizedIterationEquation μ₁ μ₂ μs γ δ η s t) :
    OriginalNormalizedIterationEquation β₁ β₂ βs γ δ η ψ (𝟙 F₂) := by
  intro K
  have h₁K := congrArg (fun z => z.app K) h₁
  have h₂K := congrArg (fun z => z.app (H₁.obj K)) h₂
  have hsK := congrArg (fun z => z.app K) hs
  have hψK := congrArg (fun z => z.app (V.obj K)) hψ
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at h₁K h₂K hsK hψK
  have hγ := γ.hom.naturality (c.hom.app K)
  dsimp only [Functor.comp_map] at hγ
  have hζ := c₂.hom.naturality ((δ.symm ≪≫ η).hom.app K)
  simp only [NatTrans.id_app]
  apply (cancel_mono (c₂.hom.app ((V ⋙ E).obj K))).mp
  calc
    _ = γ.hom.app (F.obj K) ≫ G₂.map (β₁.app K) ≫
        β₂.app (H₁.obj K) ≫ c₂.hom.app (H₂.obj (H₁.obj K)) ≫
        M₂.map ((δ.symm ≪≫ η).hom.app K) := by
      simp only [Category.assoc]
      rw [hζ]
      rfl
    _ = γ.hom.app (F.obj K) ≫
        G₂.map (β₁.app K ≫ c₁.hom.app (H₁.obj K)) ≫
        μ₂.app (H₁.obj K) ≫ M₂.map ((δ.symm ≪≫ η).hom.app K) := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z => γ.hom.app (F.obj K) ≫ G₂.map (β₁.app K) ≫ z ≫
          M₂.map ((δ.symm ≪≫ η).hom.app K)) h₂K.symm
    _ = G.map (c.hom.app K) ≫ γ.hom.app (M.obj K) ≫ G₂.map (μ₁.app K) ≫
        μ₂.app (H₁.obj K) ≫ M₂.map ((δ.symm ≪≫ η).hom.app K) := by
      rw [← h₁K]
      simp only [Functor.map_comp, ← Category.assoc]
      rw [← hγ]
    _ = G.map (c.hom.app K) ≫ μs.app K ≫ s.hom.app (V.obj K) ≫
        t.app ((V ⋙ E).obj K) := by rw [hm K]
    _ = βs.app K ≫ cs.hom.app (V.obj K) ≫ s.hom.app (V.obj K) ≫
        t.app ((V ⋙ E).obj K) := by
      rw [← Category.assoc, hsK]
      simp only [Category.assoc]
    _ = _ := by
      simpa only [Functor.comp_obj, Category.assoc, Category.comp_id] using
        congrArg (fun z => βs.app K ≫ z) hψK

end CategoryTheory
