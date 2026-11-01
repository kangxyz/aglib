/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# Consecutive exchange pasting through specified original model comparisons

Only the three actual comparison squares and the original model pasting are
used. Concrete consumers must prove all three comparison squares, including
the total one; this lemma does not assume an unproved geometric pasting law.
-/

@[expose] public section
namespace CategoryTheory

universe uA₀ uB₀ uA₁ uB₁ uA₂ uB₂ vA₀ vB₀ vA₁ vB₁ vA₂ vB₂


variable {A₀ : Type uA₀} {B₀ : Type uB₀} {A₁ : Type uA₁} {B₁ : Type uB₁} {A₂ : Type uA₂}
  {B₂ : Type uB₂}
  [Category.{vA₀} A₀] [Category.{vB₀} B₀] [Category.{vA₁} A₁] [Category.{vB₁} B₁]
  [Category.{vA₂} A₂] [Category.{vB₂} B₂]
  {R₀ M₀ : A₀ ⥤ B₀} {R₁ M₁ : A₁ ⥤ B₁} {R₂ M₂ : A₂ ⥤ B₂}
  {G₁ : B₀ ⥤ B₁} {G₂ : B₁ ⥤ B₂} {G : B₀ ⥤ B₂}
  {H₁ : A₀ ⥤ A₁} {H₂ : A₁ ⥤ A₂} {H : A₀ ⥤ A₂}

/-- The whole square of the two original model comparisons and exchanges. -/
def ExchangeModelComparisonEquation
    (c₀ : R₀ ≅ M₀) (c₁ : R₁ ≅ M₁)
    (β : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (μ : M₀ ⋙ G₁ ⟶ H₁ ⋙ M₁) : Prop :=
  Functor.whiskerRight c₀.hom G₁ ≫ μ = β ≫ Functor.whiskerLeft H₁ c₁.hom

/-- Original isomorphism-level model independence yields the same whole map square. -/
theorem exchangeModelComparisonEquation_of_iso
    (c₀ : R₀ ≅ M₀) (c₁ : R₁ ≅ M₁)
    (β : R₀ ⋙ G₁ ≅ H₁ ⋙ R₁) (μ : M₀ ⋙ G₁ ≅ H₁ ⋙ M₁)
    (h : Functor.isoWhiskerRight c₀ G₁ ≪≫ μ = β ≪≫ Functor.isoWhiskerLeft H₁ c₁) :
    ExchangeModelComparisonEquation c₀ c₁ β.hom μ.hom :=
  congrArg Iso.hom h

/-- Three proved original model squares transport the original consecutive
pasting equation to the chosen functors. No exchange invertibility is needed. -/
theorem actualHorizontalMateEquation_transport
    (c₀ : R₀ ≅ M₀) (c₁ : R₁ ≅ M₁) (c₂ : R₂ ≅ M₂)
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β : R₀ ⋙ G ⟶ H ⋙ R₂)
    (μ₁ : M₀ ⋙ G₁ ⟶ H₁ ⋙ M₁) (μ₂ : M₁ ⋙ G₂ ⟶ H₂ ⋙ M₂)
    (μ : M₀ ⋙ G ⟶ H ⋙ M₂)
    (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)
    (h₁ : ExchangeModelComparisonEquation c₀ c₁ β₁ μ₁)
    (h₂ : ExchangeModelComparisonEquation c₁ c₂ β₂ μ₂)
    (h : ExchangeModelComparisonEquation c₀ c₂ β μ)
    (hm : ∀ K, ActualHorizontalMateEquation μ₁ μ₂ μ γ δ K) (K : A₀) :
    ActualHorizontalMateEquation β₁ β₂ β γ δ K := by
  have h₁K := congrArg (fun t => t.app K) h₁
  have h₂K := congrArg (fun t => t.app (H₁.obj K)) h₂
  have hK := congrArg (fun t => t.app K) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁K h₂K hK
  have hγ : G.map (c₀.hom.app K) ≫ γ.app (M₀.obj K) =
      γ.app (R₀.obj K) ≫ G₂.map (G₁.map (c₀.hom.app K)) :=
    γ.naturality (c₀.hom.app K)
  have hδ : R₂.map (δ.app K) ≫ c₂.hom.app (H₂.obj (H₁.obj K)) =
      c₂.hom.app (H.obj K) ≫ M₂.map (δ.app K) := c₂.hom.naturality (δ.app K)
  change γ.app (R₀.obj K) ≫ G₂.map (β₁.app K) ≫ β₂.app (H₁.obj K) =
    β.app K ≫ R₂.map (δ.app K)
  apply (cancel_mono (c₂.hom.app (H₂.obj (H₁.obj K)))).mp
  calc
    _ = γ.app (R₀.obj K) ≫ G₂.map (β₁.app K ≫ c₁.hom.app (H₁.obj K)) ≫
        μ₂.app (H₁.obj K) := by
      simp only [Category.assoc, Functor.map_comp]
      rw [← h₂K]
    _ = (γ.app (R₀.obj K) ≫ G₂.map (G₁.map (c₀.hom.app K))) ≫
        G₂.map (μ₁.app K) ≫ μ₂.app (H₁.obj K) := by
      rw [← h₁K]
      simp only [Functor.map_comp, Category.assoc]
    _ = G.map (c₀.hom.app K) ≫
        (γ.app (M₀.obj K) ≫ G₂.map (μ₁.app K) ≫ μ₂.app (H₁.obj K)) := by
      rw [← hγ]
      simp only [Category.assoc]
    _ = G.map (c₀.hom.app K) ≫ μ.app K ≫ M₂.map (δ.app K) := by rw [hm K]
    _ = β.app K ≫ c₂.hom.app (H.obj K) ≫ M₂.map (δ.app K) := by
      rw [← Category.assoc, hK, Category.assoc]
    _ = _ := by rw [← hδ, Category.assoc]

end CategoryTheory
