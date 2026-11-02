/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchangeTarget

/-! # Target coherence after the original source restriction -/

@[expose] public noncomputable section
namespace CategoryTheory
open CategoryTheory.Functor
variable {A B C A' B' T₀ T₁ P P' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* A'] [Category* B']
  [Category* T₀] [Category* T₁] [Category* P] [Category* P']
  {J : A ⥤ B} {R : B ⥤ C} {G₀ : C ⥤ T₀} {G₁ : C ⥤ T₁}
  {H : B ⥤ B'} {R₀ : B' ⥤ T₀} {R₁ : B' ⥤ T₁} {G' : A ⥤ A'} {J' : A' ⥤ B'}
  {E : T₀ ⥤ T₁} {W : P ⥤ A} {W' : P' ⥤ A'} {V : P ⥤ P'}

/-- The original two-stage exchange restriction preserves the canonical target square. -/
theorem compositeExchange_target_restriction
    (β₀ : R ⋙ G₀ ⟶ H ⋙ R₀) (β₁ : R ⋙ G₁ ⟶ H ⋙ R₁)
    (e : J ⋙ H ≅ G' ⋙ J') (e' : W ⋙ G' ≅ V ⋙ W')
    (s : G₀ ⋙ E ≅ G₁) (t : R₀ ⋙ E ≅ R₁)
    (h : whiskerRight β₀ E ≫ (associator _ _ _).hom ≫ whiskerLeft H t.hom =
      (associator _ _ _).hom ≫ whiskerLeft R s.hom ≫ β₁)
    (γ₀ : (W ⋙ (J ⋙ R)) ⋙ G₀ ⟶ V ⋙ (W' ⋙ (J' ⋙ R₀)))
    (γ₁ : (W ⋙ (J ⋙ R)) ⋙ G₁ ⟶ V ⋙ (W' ⋙ (J' ⋙ R₁)))
    (hγ₀ : γ₀ = compositeExchange (compositeExchange β₀ e) e')
    (hγ₁ : γ₁ = compositeExchange (compositeExchange β₁ e) e') :
    whiskerRight γ₀ E ≫ (associator _ _ _).hom ≫
        whiskerLeft V ((associator (W' ⋙ J') R₀ E).hom ≫ whiskerLeft (W' ⋙ J') t.hom) =
      (associator _ _ _).hom ≫ whiskerLeft (W ⋙ (J ⋙ R)) s.hom ≫ γ₁ := by
  subst γ₀
  subst γ₁
  have h₀ := compositeExchange_target β₀ β₁ e s t h
  have h₁ := compositeExchange_target (compositeExchange β₀ e)
    (compositeExchange β₁ e) e' s
    (associator J' R₀ E ≪≫ isoWhiskerLeft J' t) h₀
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Iso.trans_hom, isoWhiskerLeft_hom, Category.id_comp,
    Functor.comp_obj] using congr_app h₁ K

end CategoryTheory
