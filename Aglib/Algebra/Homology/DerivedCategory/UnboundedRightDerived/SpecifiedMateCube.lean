/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactMateCube

/-! # A whole cube for four specified original mates

Keep all four actual mate transformations as parameters before evaluating their
components. The consumer supplies proved whole-map equations, never merely
isomorphic objects or invertibility of the maps to be identified.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor CategoryTheory.TwoSquare

universe uA vA uB vB uC vC uD vD uA' vA' uB' vB' uC' vC' uD' vD'

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {A' : Type uA'} [Category.{vA'} A'] {B' : Type uB'} [Category.{vB'} B']
  {C' : Type uC'} [Category.{vC'} C'] {D' : Type uD'} [Category.{vD'} D']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : C' ⥤ D'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- The literal cube equation for specified transformations follows from their
four original mate equations and the whole left-adjoint cube. -/
theorem horizontalMateCubeEquation_of_specified_mates
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (a' : L₁' ⊣ R₁') (b' : L₂' ⊣ R₂')
    (s₁ : QA ⋙ L₁' ⟶ L₁ ⋙ QB) (s₂ : QC ⋙ L₂' ⟶ L₂ ⋙ QD)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (γ : QA ⋙ G' ⟶ G ⋙ QC) (δ : QB ⋙ H' ⟶ H ⋙ QD)
    (d₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁') (d₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂')
    (μ : R₁ ⋙ G ⟶ H ⋙ R₂) (μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hs₁ : (mateEquiv a a' (TwoSquare.mk _ _ _ _ s₁)).natTrans = d₁)
    (hs₂ : (mateEquiv b b' (TwoSquare.mk _ _ _ _ s₂)).natTrans = d₂)
    (hμ : (mateEquiv a b (TwoSquare.mk _ _ _ _ α)).natTrans = μ)
    (hμ' : (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α')).natTrans = μ')
    (hc : ∀ X, L₂'.map (γ.app X) ≫ s₂.app (G.obj X) ≫ QD.map (α.app X) =
      α'.app (QA.obj X) ≫ H'.map (s₁.app X) ≫ δ.app (L₁.obj X)) :
    HorizontalMateCubeEquation d₁ d₂ μ μ' γ δ := by
  intro K
  have hleft : ∀ X, L₂'.map (γ.app X) ≫
      ((TwoSquare.mk _ _ _ _ α) ≫ₕ (TwoSquare.mk _ _ _ _ s₂)).app X =
      ((TwoSquare.mk _ _ _ _ s₁) ≫ₕ (TwoSquare.mk _ _ _ _ α')).app X ≫
        δ.app (L₁.obj X) := by
    intro X
    simpa only [TwoSquare.hComp_app, Category.assoc] using hc X
  have hm := mateEquiv_horizontal_cube a b a' b'
    (TwoSquare.mk _ _ _ _ s₁) (TwoSquare.mk _ _ _ _ s₂)
    (TwoSquare.mk _ _ _ _ α) (TwoSquare.mk _ _ _ _ α') γ δ hleft K
  change G'.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ s₁)).natTrans.app K) ≫
      (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α')).natTrans.app (QB.obj K) ≫
      R₂'.map (δ.app K) = γ.app (R₁.obj K) ≫
      QC.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ α)).natTrans.app K) ≫
      (mateEquiv b b' (TwoSquare.mk _ _ _ _ s₂)).natTrans.app (H.obj K) at hm
  rw [hs₁, hs₂, hμ, hμ'] at hm
  exact hm

end CategoryTheory
