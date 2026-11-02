/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalNormalization

/-! # Pasting specified original left-adjoint comparisons

This abstract mate argument is shared by unbounded exact localization. It uses
only the original squares and their proved mate equations, not any derived
boundedness property.
-/

@[expose] public noncomputable section

open CategoryTheory TwoSquare

universe uA vA uB vB uC vC uD vD
universe uA₀ vA₀ uA₁ vA₁ uA₂ vA₂ uB₀ vB₀
universe uB₁ vB₁ uB₂ vB₂

namespace CategoryTheory

private theorem mateEquiv_reflects_top_bottom
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vA} A] [Category.{vB} B]
      [Category.{vC} C] [Category.{vD} D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁ L₂ H')
    (γ : G ⟶ G') (δ : H ⟶ H')
    (h : ∀ K, γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α').app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K)) (K : A) :
    L₂.map (γ.app K) ≫ α'.app K = α.app K ≫ δ.app (L₁.obj K) := by
  have he : (mateEquiv adj₁ adj₂ α').whiskerRight γ =
      (mateEquiv adj₁ adj₂ α).whiskerLeft δ := by
    ext X
    exact h X
  rw [← mateEquiv_whiskerTop, ← mateEquiv_whiskerBottom] at he
  exact congrArg (fun t => t.app K) ((mateEquiv adj₁ adj₂).injective he)

private theorem forward_pasting_of_inverse
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vA} A] [Category.{vB} B]
      [Category.{vC} C] [Category.{vD} D]
    {J : A ⥤ B} {I : C ⥤ D} {F F₂ : B ⥤ D}
    {G G' : A ⥤ C}
    (e : J ⋙ F ≅ G ⋙ I) (d : J ⋙ F₂ ≅ G' ⋙ I)
    (c : F ≅ F₂) (g : G ≅ G')
    (h : ∀ K, I.map (g.hom.app K) ≫ d.inv.app K = e.inv.app K ≫ c.hom.app (J.obj K))
    (K : A) :
    c.hom.app (J.obj K) ≫ d.hom.app K = e.hom.app K ≫ I.map (g.hom.app K) := by
  have hh := congrArg (fun t => e.hom.app K ≫ t ≫ d.hom.app K) (h K)
  simpa only [Category.assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id, Functor.comp_obj] using hh.symm

/-- The whole proposition for original open-comparison pasting. -/
def LeftComparisonPastingEquation
    {A₀ : Type uA₀} {A₁ : Type uA₁} {A₂ : Type uA₂} {B₀ : Type uB₀}
  {B₁ : Type uB₁} {B₂ : Type uB₂}
    [Category.{vA₀} A₀] [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vB₀} B₀] [Category.{vB₁} B₁] [Category.{vB₂} B₂]
    {J₀ : A₀ ⥤ B₀} {J₁ : A₁ ⥤ B₁} {J₂ : A₂ ⥤ B₂}
    {G₁ : A₀ ⥤ A₁} {G₂ : A₁ ⥤ A₂} {G : A₀ ⥤ A₂}
    {F₁ : B₀ ⥤ B₁} {F₂ : B₁ ⥤ B₂} {F : B₀ ⥤ B₂}
    (e₁ : J₀ ⋙ F₁ ≅ G₁ ⋙ J₁) (e₂ : J₁ ⋙ F₂ ≅ G₂ ⋙ J₂)
    (e : J₀ ⋙ F ≅ G ⋙ J₂) (cg : G ≅ G₁ ⋙ G₂) (cf : F ≅ F₁ ⋙ F₂) : Prop :=
  ∀ K, cf.hom.app (J₀.obj K) ≫ F₂.map (e₁.hom.app K) ≫ e₂.hom.app (G₁.obj K) =
    e.hom.app K ≫ J₂.map (cg.hom.app K)

/-- Original inverse-mate pasting determines the forward left-adjoint square. -/
theorem openComparison_pasting_of_mates
    {A₀ : Type uA₀} {A₁ : Type uA₁} {A₂ : Type uA₂} {B₀ : Type uB₀}
  {B₁ : Type uB₁} {B₂ : Type uB₂}
    [Category.{vA₀} A₀] [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vB₀} B₀] [Category.{vB₁} B₁] [Category.{vB₂} B₂]
    {J₀ : A₀ ⥤ B₀} {J₁ : A₁ ⥤ B₁} {J₂ : A₂ ⥤ B₂}
    {R₀ : B₀ ⥤ A₀} {R₁ : B₁ ⥤ A₁} {R₂ : B₂ ⥤ A₂}
    {G₁ : A₀ ⥤ A₁} {G₂ : A₁ ⥤ A₂} {G : A₀ ⥤ A₂}
    {F₁ : B₀ ⥤ B₁} {F₂ : B₁ ⥤ B₂} {F : B₀ ⥤ B₂}
    (a₀ : J₀ ⊣ R₀) (a₁ : J₁ ⊣ R₁) (a₂ : J₂ ⊣ R₂)
    (e₁ : J₀ ⋙ F₁ ≅ G₁ ⋙ J₁) (e₂ : J₁ ⋙ F₂ ≅ G₂ ⋙ J₂)
    (e : J₀ ⋙ F ≅ G ⋙ J₂) (cg : G ≅ G₁ ⋙ G₂) (cf : F ≅ F₁ ⋙ F₂)
    (β₁ : TwoSquare R₀ F₁ G₁ R₁) (β₂ : TwoSquare R₁ F₂ G₂ R₂)
    (β : TwoSquare R₀ F G R₂)
    (he₁ : mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ e₁.inv) = β₁)
    (he₂ : mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ e₂.inv) = β₂)
    (he : mateEquiv a₀ a₂ (TwoSquare.mk _ _ _ _ e.inv) = β)
    (hβ : ∀ N, VerticalSquareEquation β₁ β₂ β cf cg N) :
    LeftComparisonPastingEquation e₁ e₂ e cg cf := by
  intro K
  let d := (Functor.associator J₀ F₁ F₂).symm ≪≫
    Functor.isoWhiskerRight e₁ F₂ ≪≫ Functor.associator G₁ J₁ F₂ ≪≫
    Functor.isoWhiskerLeft G₁ e₂ ≪≫ (Functor.associator G₁ G₂ J₂).symm
  have hd (M : A₀) : J₂.map (cg.hom.app M) ≫ d.inv.app M =
      e.inv.app M ≫ cf.hom.app (J₀.obj M) := by
    have hm := mateEquiv_reflects_top_bottom a₀ a₂
      (TwoSquare.mk _ _ _ _ e.inv)
      ((TwoSquare.mk _ _ _ _ e₁.inv) ≫ₕ (TwoSquare.mk _ _ _ _ e₂.inv))
      cg.hom cf.hom (by
        intro N
        rw [mateEquiv_vcomp, he₁, he₂, he]
        simpa only [VerticalSquareEquation, TwoSquare.vComp_app] using hβ N) M
    simpa only [d, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, TwoSquare.hComp_app] using hm
  have hf := forward_pasting_of_inverse e d cf cg hd K
  simpa only [d, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id] using hf


end CategoryTheory
