/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.UnitComparison

/-!
# Original-unit uniqueness of a derived mate

A comparison satisfying the original complex-unit equation is the installed
derived mate. The proof uses the native right-derived universal property after
postcomposition; it never cancels a nonexact right-derived unit. The current
consumer is additive scalar forgetting for genuine module sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory.Functor

namespace CategoryTheory

universe uA vA wA uB vB wB uC vC wC uD vD wD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  [EnoughInjectives D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  [G.Additive] [H.Additive] [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  (α : TwoSquare G L₁ L₂ H)
  (αD : TwoSquare G.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
    L₂.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)

/-- The actual complex-unit equation determines the original derived mate uniquely. -/
theorem derivedMate_eq_of_originalUnit
    (h : ∀ Z : CochainComplex.Plus A, ExactComparisonSquareEquation L₁ H G L₂ α αD Z)
    (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
      H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)
    (hβ : ∀ K : CochainComplex.Plus B,
      G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
          β.app (DerivedCategory.Plus.Q.obj K) ≫
          R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
        G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K) ≫
          DerivedCategory.Plus.Q.map (((mateEquiv adj₁ adj₂ α).mapCochainComplexPlus).app K) ≫
          R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K)) :
    (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus αD).natTrans = β := by
  let := R₁.isRightDerivedFunctor_rightDerivedFunctorPlus_postcomp G.rightDerivedFunctorPlus
  apply (R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).rightDerived_ext
    (whiskerRight R₁.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus ≫
      (associator _ _ _).hom) (CochainComplex.Plus.quasiIso B)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app]
  simp only [Category.comp_id]
  apply (cancel_mono (R₂.rightDerivedFunctorPlus.map
    (H.rightDerivedFunctorPlusExactComparison.hom.app K))).mp
  simpa only [Category.assoc] using
    (derivedMateUnitEquation_of_exactSquare adj₁ adj₂ α αD h K).trans (hβ K).symm

end CategoryTheory
