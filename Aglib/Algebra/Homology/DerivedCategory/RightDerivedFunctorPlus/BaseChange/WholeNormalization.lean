/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CoherenceDiagram
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SquarePasting

/-! # Normalize actual exchange squares before taking components -/

@[expose] public section

namespace CategoryTheory

section WholeHorizontalSquare
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G₁ : A ⥤ B} {G₂ : B ⥤ C} {L₂ : C ⥤ D} {L₁ : B ⥤ E}
  {H₂ : E ⥤ D} {L₀ : A ⥤ F} {H₁ : F ⥤ E}
  {G : A ⥤ C} {H : F ⥤ D}
  (α₁ : G₁ ⋙ L₁ ⟶ L₀ ⋙ H₁) (α₂ : G₂ ⋙ L₂ ⟶ L₁ ⋙ H₂)
  (α : G ⋙ L₂ ⟶ L₀ ⋙ H) (γ : G ⟶ G₁ ⋙ G₂) (θ : H ⟶ H₁ ⋙ H₂)

/-- Horizontal square coherence in the whole functor category, with native associators. -/
def WholeHorizontalSquareEquation : Prop :=
  Functor.whiskerRight γ L₂ ≫ (Functor.associator G₁ G₂ L₂).hom ≫
      Functor.whiskerLeft G₁ α₂ ≫ (Functor.associator G₁ L₁ H₂).inv ≫
      Functor.whiskerRight α₁ H₂ ≫ (Functor.associator L₀ H₁ H₂).hom =
    α ≫ Functor.whiskerLeft L₀ θ

/-- Only the final short square is evaluated; no long component chain is exposed. -/
theorem wholeHorizontalSquare_app
    (h : WholeHorizontalSquareEquation α₁ α₂ α γ θ) (X : A) :
    HorizontalSquareEquation (TwoSquare.mk _ _ _ _ α₁) (TwoSquare.mk _ _ _ _ α₂)
      (TwoSquare.mk _ _ _ _ α) γ θ X := by
  have hc := congrArg (fun η => η.app X) h
  simpa only [HorizontalSquareEquation, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using hc

end WholeHorizontalSquare

section WholeNormalization
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G₁ : A ⥤ B} {G₂ : B ⥤ C} {L₂ : C ⥤ D} {L₁ : B ⥤ E}
  {H₂ : E ⥤ D} {L₀ : A ⥤ F} {H₁ : F ⥤ E}
  {G : A ⥤ C} {H : F ⥤ D} {M N : A ⥤ E}
  {Q R : B ⥤ D} {P T : A ⥤ D}
  (γ : G ≅ G₁ ⋙ G₂) (θ : H ≅ H₁ ⋙ H₂)
  (p : P ≅ G ⋙ L₂) (b : Q ≅ G₂ ⋙ L₂) (t₂ : Q ≅ R) (c : R ≅ L₁ ⋙ H₂)
  (d : M ≅ G₁ ⋙ L₁) (t₁ : M ≅ N) (e : N ≅ L₀ ⋙ H₁)
  (τ : P ≅ T) (u : T ≅ L₀ ⋙ H)
  (α₁ : G₁ ⋙ L₁ ≅ L₀ ⋙ H₁) (α₂ : G₂ ⋙ L₂ ≅ L₁ ⋙ H₂)
  (α : G ⋙ L₂ ≅ L₀ ⋙ H)

/-- Normalize the entire native comparison chain before taking any component. -/
theorem exchangeCoherence_normalize_whole
    (h₁ : α₁ = d.symm ≪≫ t₁ ≪≫ e)
    (h₂ : α₂ = b.symm ≪≫ t₂ ≪≫ c)
    (h : α = p.symm ≪≫ τ ≪≫ u)
    (hc : WhiskeredComparisonChainEquation γ d e p.hom
      (Functor.whiskerLeft G₁ b.inv) (Functor.whiskerLeft G₁ t₂.hom)
      (Functor.whiskerLeft G₁ c.hom) (Functor.whiskerRight t₁.hom H₂)
      τ.hom u.hom (Functor.whiskerLeft L₀ θ.hom)) :
    WholeHorizontalSquareEquation α₁.hom α₂.hom α.hom γ.hom θ.hom := by
  subst α₁
  subst α₂
  subst α
  have hc' := (Iso.eq_inv_comp p).mpr hc
  simpa only [WholeHorizontalSquareEquation, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc] using hc'

end WholeNormalization

end CategoryTheory
