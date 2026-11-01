/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import Aglib.CategoryTheory.NatTrans.CartesianSourceExchange
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
  {F : A ⥤ B} {F₁ : A₁ ⥤ B₁} {F₂ : A₂ ⥤ B₂} {Fs : As ⥤ B₂}
  {G₁ : B ⥤ B₁} {G₂ : B₁ ⥤ B₂} {G : B ⥤ B₂}
  {H₁ : A ⥤ A₁} {H₂ : A₁ ⥤ A₂} {H : A ⥤ A₂} {V : A ⥤ As} {E : As ⥤ A₂}

/-- Cancellation of the same original source isomorphism recovers the literal
pasting equation of the original transported exchanges. -/
theorem cartesianSourceExchange_pasting_conclusion
    (β₁ : F ⋙ G₁ ⟶ H₁ ⋙ F₁) (β₂ : F₁ ⋙ G₂ ⟶ H₂ ⋙ F₂)
    (βs : F ⋙ G ≅ V ⋙ Fs) (γ : G ≅ G₁ ⋙ G₂)
    (δ : H ≅ H₁ ⋙ H₂) (η : H ≅ V ⋙ E) (s : Fs ≅ E ⋙ F₂)
    (hp : OriginalNormalizedIterationEquation β₁ β₂ βs.hom γ δ η s (𝟙 F₂)) (K : A) :
    ActualHorizontalMateEquation β₁ β₂ (cartesianSourceExchange βs s η).hom
      γ.hom δ.hom K := by
  have hpK := hp K
  dsimp only [Functor.comp_obj, NatTrans.id_app] at hpK
  simp only [Category.comp_id] at hpK
  change γ.hom.app (F.obj K) ≫ G₂.map (β₁.app K) ≫ β₂.app (H₁.obj K) = _
  apply (cancel_mono (F₂.map ((δ.symm ≪≫ η).hom.app K))).mp
  rw [cartesianSourceExchange_hom_app]
  simp only [Category.assoc]
  rw [hpK]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ← F₂.map_comp, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [F₂.map_id, Category.comp_id]

end CategoryTheory
