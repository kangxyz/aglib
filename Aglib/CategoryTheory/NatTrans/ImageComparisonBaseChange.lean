/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnitComparisonNaturality
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeNaturality
public import Aglib.CategoryTheory.NatTrans.CompositeExchange
public import Aglib.CategoryTheory.NatTrans.OverComparisonEquation
public import Aglib.CategoryTheory.Functor.ImageComparison

/-!
# Whole naturality of original image comparisons and pasted exchanges

This abstract boundary composes the actual unit-comparison square with the
actual structural-image square. Concrete consumers supply both proved squares;
the output is exactly the original whole natural-transformation equality.
-/

@[expose] public section

universe uU vU uC vC uD vD uS vS uU' vU' uC' vC' uD' vD' uT vT

namespace CategoryTheory

variable {U : Type uU} {C : Type uC} {D : Type uD} {S : Type uS}
  {U' : Type uU'} {C' : Type uC'} {D' : Type uD'} {T : Type uT}
  [Category.{vU} U] [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
  [Category.{vU'} U'] [Category.{vC'} C'] [Category.{vD'} D'] [Category.{vT} T]
  {J₁ : U ⥤ C} {J₂ : U ⥤ D} {R : C ⥤ D} {P₁ : C ⥤ S} {P₂ : D ⥤ S}
  {F : S ⥤ T} {V : U ⥤ U'} {Q₁ : C ⥤ C'} {Q₂ : D ⥤ D'}
  {R' : C' ⥤ D'} {P₁' : C' ⥤ T} {P₂' : D' ⥤ T}
  {J₁' : U' ⥤ C'} {J₂' : U' ⥤ D'}

/-- The whole original image-comparison/exchange naturality equation. -/
def ImageComparisonBaseChangeEquation
    (δ : J₂ ⟶ J₁ ⋙ R) (δ' : J₂' ⟶ J₁' ⋙ R')
    (τ : R ⋙ P₂ ≅ P₁) (τ' : R' ⋙ P₂' ≅ P₁')
    (β₁ : P₁ ⋙ F ⟶ Q₁ ⋙ P₁') (β₂ : P₂ ⋙ F ⟶ Q₂ ⋙ P₂')
    (e₁ : J₁ ⋙ Q₁ ≅ V ⋙ J₁') (e₂ : J₂ ⋙ Q₂ ≅ V ⋙ J₂') : Prop :=
  Functor.whiskerRight (imageComparison δ τ) F ≫ compositeExchange β₁ e₁ =
    compositeExchange β₂ e₂ ≫ Functor.whiskerLeft V (imageComparison δ' τ')

/-- The actual original unit and structural-image squares prove whole
naturality without expanding any concrete adjunction in the consumer. -/
theorem imageComparisonBaseChangeEquation_of_squares
    (δ : J₂ ⟶ J₁ ⋙ R) (δ' : J₂' ⟶ J₁' ⋙ R')
    (τ : R ⋙ P₂ ≅ P₁) (τ' : R' ⋙ P₂' ≅ P₁')
    (β₁ : P₁ ⋙ F ⟶ Q₁ ⋙ P₁') (β₂ : P₂ ⋙ F ⟶ Q₂ ⋙ P₂')
    (βR : R ⋙ Q₂ ⟶ Q₁ ⋙ R')
    (e₁ : J₁ ⋙ Q₁ ≅ V ⋙ J₁') (e₂ : J₂ ⋙ Q₂ ≅ V ⋙ J₂')
    (hδ : UnitComparisonNaturalityEquation βR e₂.hom e₁.hom δ δ')
    (hτ : OverComparisonBaseChangeEquation τ τ' β₁ β₂ βR) :
    ImageComparisonBaseChangeEquation δ δ' τ τ' β₁ β₂ e₁ e₂ := by
  apply NatTrans.ext
  funext K
  have ht := hτ (J₁.obj K)
  simp only [← Category.assoc] at ht
  have ht' := (Iso.comp_inv_eq (τ'.app (Q₁.obj (J₁.obj K)))).mp ht
  simp only [Category.assoc] at ht'
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    imageComparison_app, compositeExchange_app, Category.assoc] using
    compositeExchange_comparison_naturality δ δ' τ.hom τ'.hom β₁ β₂ βR
      e₁.hom e₂.hom K (hδ K) ht'

end CategoryTheory
