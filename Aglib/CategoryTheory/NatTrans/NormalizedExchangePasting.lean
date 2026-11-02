/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# Pasting original exchanges through specified normalization maps

The original consecutive exchange equation and the actual intermediate
normalization square imply consecutive pasting for the specified normalized
maps. Both whole defining formulas are retained, so concrete consumers need not
unfold their isomorphism constructors.
-/

@[expose] public section

namespace CategoryTheory

universe uA₀ uB₀ uA₁ uB₁ uA₂ uB₂ vA₀ vB₀ vA₁ vB₁ vA₂ vB₂


variable {A₀ : Type uA₀} {B₀ : Type uB₀} {A₁ : Type uA₁} {B₁ : Type uB₁} {A₂ : Type uA₂}
  {B₂ : Type uB₂}
  [Category.{vA₀} A₀] [Category.{vB₀} B₀] [Category.{vA₁} A₁]
  [Category.{vB₁} B₁] [Category.{vA₂} A₂] [Category.{vB₂} B₂]
  {R₀ : A₀ ⥤ B₀} {R₁ N₁ : A₁ ⥤ B₁} {R₂ N₂ : A₂ ⥤ B₂}
  {G₁ : B₀ ⥤ B₁} {G₂ : B₁ ⥤ B₂} {G : B₀ ⥤ B₂}
  {H₁ : A₀ ⥤ A₁} {H₂ : A₁ ⥤ A₂} {H : A₀ ⥤ A₂}

/-- Actual exchange pasting survives the specified normalization, using the
actual intermediate normalization square and the original whole map formulas. -/
theorem normalizedExchange_pasting
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β : R₀ ⋙ G ⟶ H ⋙ R₂) (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)
    (n₁ : R₁ ⟶ N₁) (n₂ : R₂ ⟶ N₂)
    (βN₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ N₁) (βN₂ : N₁ ⋙ G₂ ⟶ H₂ ⋙ N₂)
    (βN : R₀ ⋙ G ⟶ H ⋙ N₂)
    (hraw : ∀ K, ActualHorizontalMateEquation β₁ β₂ β γ δ K)
    (hslide : ExchangeNaturalityEquation n₁ βN₂ β₂ n₂)
    (hfirst : βN₁ = β₁ ≫ Functor.whiskerLeft H₁ n₁)
    (hfinal : βN = β ≫ Functor.whiskerLeft H n₂) :
    ∀ K, ActualHorizontalMateEquation βN₁ βN₂ βN γ δ K := by
  intro K
  have hs := congrArg (fun t => t.app (H₁.obj K)) hslide
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hs
  have hf := congrArg (fun t => t.app K) hfirst
  have he := congrArg (fun t => t.app K) hfinal
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf he
  have hn := n₂.naturality (δ.app K)
  change γ.app (R₀.obj K) ≫ G₂.map (βN₁.app K) ≫ βN₂.app (H₁.obj K) =
    βN.app K ≫ N₂.map (δ.app K)
  rw [hf, G₂.map_comp, Category.assoc, hs]
  have hr := congrArg (fun t => t ≫ n₂.app (H₂.obj (H₁.obj K)))
    (actualHorizontalMateEquation_eq β₁ β₂ β γ δ K (hraw K))
  simp only [Category.assoc] at hr
  rw [hr, he]
  simpa only [Functor.comp_obj, Category.assoc] using
    congrArg (fun t => β.app K ≫ t) hn

end CategoryTheory
