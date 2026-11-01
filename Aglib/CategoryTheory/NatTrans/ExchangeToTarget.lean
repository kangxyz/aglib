/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.NatTrans.ExchangePastingTransport
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation

/-! # Transport of the same comparison through an actual exchange model square -/
@[expose] public section
namespace CategoryTheory
open CategoryTheory.Functor
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {R M F : A ⥤ B} {R' M' F' : A' ⥤ B'} {G : B ⥤ B'} {H : A ⥤ A'}

/-- An actual exchange commutes with the specified maps to ordinary images. -/
def ExchangeToTargetEquation (b : R ⟶ F) (b' : R' ⟶ F')
    (β : R ⋙ G ⟶ H ⋙ R') (γ : F ⋙ G ⟶ H ⋙ F') : Prop :=
  β ≫ whiskerLeft H b' = whiskerRight b G ≫ γ

/-- Descent uses the proved model square and the two proved same-map comparisons. -/
theorem exchangeToTarget_transport (c : R ≅ M) (c' : R' ≅ M')
    (b : R ⟶ F) (b' : R' ⟶ F') (m : M ⟶ F) (m' : M' ⟶ F')
    (β : R ⋙ G ⟶ H ⋙ R') (μ : M ⋙ G ⟶ H ⋙ M') (γ : F ⋙ G ⟶ H ⋙ F')
    (hc : TargetComparisonEquation c.hom m b)
    (hc' : TargetComparisonEquation c'.hom m' b')
    (hβ : ExchangeModelComparisonEquation c c' β μ)
    (hμ : ExchangeToTargetEquation m m' μ γ) :
    ExchangeToTargetEquation b b' β γ := by
  change β ≫ whiskerLeft H b' = whiskerRight b G ≫ γ
  rw [← hc, ← hc', whiskerLeft_comp, whiskerRight_comp]
  rw [← Category.assoc, ← hβ, Category.assoc, hμ, ← Category.assoc]

/-- Postcomposing the target model by a known same-map comparison retains compatibility. -/
theorem exchangeToTarget_postcompose (b : R ⟶ F) (b' : R' ⟶ F') (m' : M' ⟶ F')
    (d : R' ⟶ M') (β : R ⋙ G ⟶ H ⋙ R') (γ : F ⋙ G ⟶ H ⋙ F')
    (hd : TargetComparisonEquation d m' b') (hβ : ExchangeToTargetEquation b b' β γ) :
    ExchangeToTargetEquation b m' (β ≫ whiskerLeft H d) γ := by
  change (β ≫ whiskerLeft H d) ≫ whiskerLeft H m' = whiskerRight b G ≫ γ
  rw [Category.assoc, ← whiskerLeft_comp, hd]
  exact hβ
end CategoryTheory
