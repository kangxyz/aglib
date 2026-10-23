/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactSquare
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HorizontalCube
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.DerivedUnit

/-!
# Original-unit compatibility of native derived mates

A specified exact-left comparison square yields an equation between the actual
right-derived units and the actual native mates. Concrete applications must prove
the comparison square; no invertibility of a right-derived unit is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open TwoSquare

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

/-- Literal original-unit compatibility for a derived mate, as a shared formula. -/
def DerivedMateUnitEquation (K : CochainComplex.Plus B) : Prop :=
  G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
      (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus αD).app
        (DerivedCategory.Plus.Q.obj K) ≫
      R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
    G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map (((mateEquiv adj₁ adj₂ α).mapCochainComplexPlus).app K) ≫
      R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K)

/-- A compatible exact-left square gives compatibility of its native mate with the
original right-derived units. No nonexact unit is cancelled. -/
theorem derivedMateUnitEquation
    (h : ∀ Z : CochainComplex.Plus A,
      L₂.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
        L₂.rightDerivedFunctorPlusExactComparison.hom.app (G.mapCochainComplexPlus.obj Z) ≫
        DerivedCategory.Plus.Q.map (α.mapCochainComplexPlus.app Z) =
      αD.app (DerivedCategory.Plus.Q.obj Z) ≫
        H.rightDerivedFunctorPlus.map (L₁.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
        H.rightDerivedFunctorPlusExactComparison.hom.app (L₁.mapCochainComplexPlus.obj Z))
    (K : CochainComplex.Plus B) : DerivedMateUnitEquation adj₁ adj₂ α αD K := by
  let s₁ := TwoSquare.mk _ _ _ _ L₁.rightDerivedFunctorPlusExactComparison.hom
  let s₂ := TwoSquare.mk _ _ _ _ L₂.rightDerivedFunctorPlusExactComparison.hom
  have hc : ∀ Z : CochainComplex.Plus A,
      L₂.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
          (α.mapCochainComplexPlus ≫ₕ s₂).app Z =
        (s₁ ≫ₕ αD).app Z ≫
          H.rightDerivedFunctorPlusExactComparison.hom.app (L₁.mapCochainComplexPlus.obj Z) := by
    intro Z
    simpa only [TwoSquare.hComp_app, s₁, s₂, Category.assoc] using h Z
  have hm := mateEquiv_horizontal_cube adj₁.mapCochainComplexPlus adj₂.mapCochainComplexPlus
    adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus s₁ s₂
    α.mapCochainComplexPlus αD G.rightDerivedFunctorPlusExactComparison.hom
    H.rightDerivedFunctorPlusExactComparison.hom hc K
  simpa only [DerivedMateUnitEquation, s₁, s₂,
    ← Adjunction.rightDerivedFunctorPlusUnit_eq_mate, mateEquiv_mapCochainComplexPlus] using hm

/-- A shared exact-square witness specializes to the literal original-unit equation. -/
theorem derivedMateUnitEquation_of_exactSquare
    (h : ∀ Z : CochainComplex.Plus A, ExactComparisonSquareEquation L₁ H G L₂ α αD Z)
    (K : CochainComplex.Plus B) : DerivedMateUnitEquation adj₁ adj₂ α αD K :=
  derivedMateUnitEquation adj₁ adj₂ α αD h K

end CategoryTheory
