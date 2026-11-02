/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Transport of an original exchange through an actual source comparison -/

@[expose] public noncomputable section
universe uA vA uA' vA' uA'' vA'' uD vD uD' vD'

namespace CategoryTheory

variable {A : Type uA} {A' : Type uA'} {A'' : Type uA''} {D : Type uD} {D' : Type uD'}
  [Category.{vA} A] [Category.{vA'} A'] [Category.{vA''} A''] [Category.{vD} D] [Category.{vD'} D']
  {F : A ⥤ D} {G : A' ⥤ D'} {H : A'' ⥤ D'} {B : D ⥤ D'}
  {V : A ⥤ A'} {E : A' ⥤ A''} {W : A ⥤ A''}

/-- Keep the original exchange, actual source comparison, and original source compositor. -/
def cartesianSourceExchange (β : F ⋙ B ≅ V ⋙ G) (ψ : G ≅ E ⋙ H)
    (c : W ≅ V ⋙ E) : F ⋙ B ≅ W ⋙ H :=
  β ≪≫ Functor.isoWhiskerLeft V ψ ≪≫ (Functor.associator V E H).symm ≪≫
    Functor.isoWhiskerRight c.symm H

/-- The transported exchange retains its literal original component formula. -/
theorem cartesianSourceExchange_hom_app
    (β : F ⋙ B ≅ V ⋙ G) (ψ : G ≅ E ⋙ H) (c : W ≅ V ⋙ E) (K : A) :
    (cartesianSourceExchange β ψ c).hom.app K =
      β.hom.app K ≫ ψ.hom.app (V.obj K) ≫ H.map (c.inv.app K) := by
  simp only [cartesianSourceExchange, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp]

/-- The same transport preserves actual canonical model squares. -/
theorem cartesianSourceExchange_model
    {F₁ : A ⥤ D} {G₁ : A' ⥤ D'} {H₁ : A'' ⥤ D'}
    (β : F ⋙ B ≅ V ⋙ G) (ψ : G ≅ E ⋙ H)
    (β₁ : F₁ ⋙ B ≅ V ⋙ G₁) (ψ₁ : G₁ ≅ E ⋙ H₁) (c : W ≅ V ⋙ E)
    (s : F ≅ F₁) (t : G ≅ G₁) (u : H ≅ H₁)
    (hβ : Functor.isoWhiskerRight s B ≪≫ β₁ = β ≪≫ Functor.isoWhiskerLeft V t)
    (hψ : t ≪≫ ψ₁ = ψ ≪≫ Functor.isoWhiskerLeft E u) :
    Functor.isoWhiskerRight s B ≪≫ cartesianSourceExchange β₁ ψ₁ c =
      cartesianSourceExchange β ψ c ≪≫ Functor.isoWhiskerLeft W u := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hb := congrArg (fun i => i.hom.app K) hβ
  have hp := congrArg (fun i => i.hom.app (V.obj K)) hψ
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hb hp ⊢
  rw [cartesianSourceExchange_hom_app, cartesianSourceExchange_hom_app]
  simp only [Category.assoc]
  rw [← Category.assoc, hb, Category.assoc, ← Category.assoc (t.hom.app _) _ _, hp]
  simp only [Category.assoc]
  exact congrArg (fun z => β.hom.app K ≫ ψ.hom.app (V.obj K) ≫ z)
    (u.hom.naturality (c.inv.app K)).symm

end CategoryTheory
