/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Original continuous transformations and exchanged adjunctions

Continuous pushforward transforms reverse the original site transformation
order. The whole exchanged map is then identified through the original four
adjunctions and their actual unit equations. Invertibility of the exchanged
map is a consequence in native applications, not an input here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.OriginalExchange

/-- Continuous pushforward reverses the original three site transformations. -/
theorem continuous_three_transforms
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {P₀ P₁ P₂ P₃ : C ⥤ D}
    [P₀.IsContinuous J K] [P₁.IsContinuous J K]
    [P₂.IsContinuous J K] [P₃.IsContinuous J K]
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) :
    Functor.sheafPushforwardContinuousNatTrans c A J K ≫
      Functor.sheafPushforwardContinuousNatTrans b A J K ≫
        Functor.sheafPushforwardContinuousNatTrans a A J K =
    Functor.sheafPushforwardContinuousNatTrans (a ≫ b ≫ c) A J K := by
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (c.app U.unop).op ≫ F.obj.map (b.app U.unop).op ≫
    F.obj.map (a.app U.unop).op = F.obj.map (a.app U.unop ≫
      b.app U.unop ≫ c.app U.unop).op
  simp only [op_comp, Functor.map_comp, Category.assoc]

/-- The three-factor isomorphism retains the supplied original hom components. -/
theorem iso_chain_hom_of_eq {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ : C} (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (p : X₀ ⟶ X₁) (q : X₁ ⟶ X₂) (r : X₂ ⟶ X₃)
    (hp : a.hom = p) (hq : b.hom = q) (hr : c.hom = r) :
    (a ≪≫ b ≪≫ c).hom = p ≫ q ≫ r := by
  simp only [Iso.trans_hom, hp, hq, hr]

/-- Naturality transports the original unit equation across the actual comparison iso. -/
theorem transported_exchange_unit
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (G : A ⥤ B) (H : D ⥤ C) (R : C ⥤ B) (N : D ⥤ A)
    {D₀ D₁ : D} (d : D₀ ≅ D₁) {B₀ : B} {C₀ C₁ : C}
    (η : B₀ ⟶ R.obj C₀) (e : C₀ ⟶ C₁) (E : C₁ ⟶ H.obj D₁)
    (θ : B₀ ⟶ G.obj (N.obj D₀))
    (ρ₀ : G.obj (N.obj D₀) ⟶ R.obj (H.obj D₀))
    (ρ₁ : G.obj (N.obj D₁) ⟶ R.obj (H.obj D₁))
    (hn : G.map (N.map d.hom) ≫ ρ₁ = ρ₀ ≫ R.map (H.map d.hom))
    (hg : η ≫ R.map e ≫ R.map E = θ ≫ G.map (N.map d.hom) ≫ ρ₁)
    (b : C₀ ⟶ H.obj D₀) (hb : b = e ≫ E ≫ H.map d.inv) :
    θ ≫ ρ₀ = η ≫ R.map b := by
  rw [hn] at hg
  have hc := congrArg (fun k => k ≫ R.map (H.map d.inv)) hg
  simp only [Category.assoc] at hc
  rw [← R.map_comp (H.map d.hom) (H.map d.inv), ← H.map_comp d.hom d.inv,
    d.hom_inv_id, H.map_id, R.map_id,
    Category.comp_id] at hc
  simpa only [hb, Functor.map_comp, Category.assoc] using hc.symm

/-- The original adjunction unit determines a morphism out of its left adjoint. -/
theorem adjunction_unit_ext {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y : D}
    (a b : L.obj X ⟶ Y)
    (h : adj.unit.app X ≫ R.map a = adj.unit.app X ≫ R.map b) : a = b :=
  (adj.homEquiv X Y).injective h

/-- The transported restriction comparison equals the original exchange from its unit equation. -/
theorem exchange_of_restriction
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (G : A ⥤ B) (H : D ⥤ C) {L₀ M₀ : A ⥤ D} {N : D ⥤ A}
    {L₁ M₁ : B ⥤ C} {R : C ⥤ B}
    (a₀ : L₀ ⊣ N) (a₁ : L₁ ⊣ R) (m₀ : M₀ ⊣ N) (m₁ : M₁ ⊣ R)
    (e₀ : L₀ ≅ M₀) (e₁ : L₁ ≅ M₁) (E : G ⋙ M₁ ≅ M₀ ⋙ H)
    (ρ : N ⋙ G ⟶ H ⋙ R) (β : G ⋙ L₁ ⟶ L₀ ⋙ H)
    (h₀ : ∀ F, a₀.unit.app F ≫ N.map (e₀.hom.app F) = m₀.unit.app F)
    (h₁ : ∀ F, a₁.unit.app F ≫ R.map (e₁.hom.app F) = m₁.unit.app F)
    (hE : ∀ F, m₁.unit.app (G.obj F) ≫ R.map (E.hom.app F) =
      G.map (m₀.unit.app F) ≫ ρ.app (M₀.obj F))
    (hβ : ∀ F, G.map (a₀.unit.app F) ≫ ρ.app (L₀.obj F) =
      a₁.unit.app (G.obj F) ≫ R.map (β.app F)) :
    (Functor.isoWhiskerLeft G e₁ ≪≫ E ≪≫ Functor.isoWhiskerRight e₀.symm H).hom = β := by
  apply NatTrans.ext
  funext F
  have hg := hE F
  rw [← h₁, ← h₀] at hg
  simp only [Category.assoc, Functor.map_comp] at hg
  have hu := transported_exchange_unit G H R N (e₀.app F)
    (a₁.unit.app (G.obj F)) (e₁.hom.app (G.obj F)) (E.hom.app F)
    (G.map (a₀.unit.app F)) (ρ.app (L₀.obj F)) (ρ.app (M₀.obj F))
    (ρ.naturality (e₀.hom.app F)) hg
    ((Functor.isoWhiskerLeft G e₁ ≪≫ E ≪≫
      Functor.isoWhiskerRight e₀.symm H).hom.app F) rfl
  exact adjunction_unit_ext a₁ _ _ (hu.symm.trans (hβ F))

end CategoryTheory.OriginalExchange
