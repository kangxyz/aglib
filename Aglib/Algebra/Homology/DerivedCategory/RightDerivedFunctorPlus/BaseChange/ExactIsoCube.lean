/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactCube
public import Aglib.CategoryTheory.Functor.CompositionCubeWhole

/-!
# Exact comparison transports whole natural-isomorphism cubes

A whole natural-isomorphism cube of exact additive functors induces the cube
of the six supplied installed bounded-below derived squares. The original
components are evaluated only after applying the generic whole-cube equation;
the original comparisons and the six exact-comparison witnesses are retained.
Scalar-forgetting comparisons consume this interface.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open CategoryTheory.Functor
open scoped TwoSquare

universe uA vA wA uB vB wB uC vC wC uD vD wD
  uA' vA' wA' uB' vB' wB' uC' vC' wC' uD' vD' wD'

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  [EnoughInjectives D]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  [EnoughInjectives A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  [EnoughInjectives B']
  {C' : Type uC'} [Category.{vC'} C'] [Abelian C'] [HasDerivedCategory.{wC'} C']
  [EnoughInjectives C']
  {D' : Type uD'} [Category.{vD'} D'] [Abelian D'] [HasDerivedCategory.{wD'} D']
  {L₁ : A ⥤ B} {L₂ : C ⥤ D} {L₁' : A' ⥤ B'} {L₂' : C' ⥤ D'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  [L₁.Additive] [L₂.Additive] [L₁'.Additive] [L₂'.Additive]
  [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
  [QA.Additive] [QB.Additive] [QC.Additive] [QD.Additive]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  [L₁'.PreservesHomology] [L₂'.PreservesHomology]
  [G.PreservesHomology] [H.PreservesHomology]
  [G'.PreservesHomology] [H'.PreservesHomology]
  [QA.PreservesHomology] [QB.PreservesHomology]
  [QC.PreservesHomology] [QD.PreservesHomology]

/-- A whole cube of the six specified original natural isomorphisms transports
to the same six supplied derived squares through their literal exact comparisons. -/
theorem rightDerivedFunctorPlus_exactHorizontalCube_of_whole
    (sL : L₁ ⋙ QB ≅ QA ⋙ L₁') (sL' : L₂ ⋙ QD ≅ QC ⋙ L₂')
    (sG : G ⋙ QC ≅ QA ⋙ G') (sH : H ⋙ QD ≅ QB ⋙ H')
    (sm : G ⋙ L₂ ≅ L₁ ⋙ H) (sa : G' ⋙ L₂' ≅ L₁' ⋙ H')
    (s₁D : TwoSquare QA.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
      L₁'.rightDerivedFunctorPlus QB.rightDerivedFunctorPlus)
    (s₂D : TwoSquare QC.rightDerivedFunctorPlus L₂.rightDerivedFunctorPlus
      L₂'.rightDerivedFunctorPlus QD.rightDerivedFunctorPlus)
    (αD : TwoSquare G.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
      L₂.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)
    (α'D : TwoSquare G'.rightDerivedFunctorPlus L₁'.rightDerivedFunctorPlus
      L₂'.rightDerivedFunctorPlus H'.rightDerivedFunctorPlus)
    (γD : TwoSquare QA.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
      G'.rightDerivedFunctorPlus QC.rightDerivedFunctorPlus)
    (δD : TwoSquare QB.rightDerivedFunctorPlus H.rightDerivedFunctorPlus
      H'.rightDerivedFunctorPlus QD.rightDerivedFunctorPlus)
    (hs₁ : ∀ Z, ExactComparisonSquareEquation L₁ QB QA L₁'
      (TwoSquare.mk _ _ _ _ sL.inv) s₁D Z)
    (hs₂ : ∀ Z, ExactComparisonSquareEquation L₂ QD QC L₂'
      (TwoSquare.mk _ _ _ _ sL'.inv) s₂D Z)
    (hα : ∀ Z, ExactComparisonSquareEquation L₁ H G L₂
      (TwoSquare.mk _ _ _ _ sm.hom) αD Z)
    (hα' : ∀ Z, ExactComparisonSquareEquation L₁' H' G' L₂'
      (TwoSquare.mk _ _ _ _ sa.hom) α'D Z)
    (hγ : ∀ Z, ExactComparisonSquareEquation G QC QA G'
      (TwoSquare.mk _ _ _ _ sG.inv) γD Z)
    (hδ : ∀ Z, ExactComparisonSquareEquation H QD QB H'
      (TwoSquare.mk _ _ _ _ sH.inv) δD Z)
    (hwhole : Functor.ComparisonCubeEquation sL sL' sG sH sm sa)
    (K : DerivedCategory.Plus A) :
    L₂'.rightDerivedFunctorPlus.map (γD.app K) ≫ (αD ≫ₕ s₂D).app K =
      (s₁D ≫ₕ α'D).app K ≫ δD.app (L₁.rightDerivedFunctorPlus.obj K) := by
  refine rightDerivedFunctorPlus_exactHorizontalCube
    (TwoSquare.mk _ _ _ _ sL.inv) (TwoSquare.mk _ _ _ _ sL'.inv)
    (TwoSquare.mk _ _ _ _ sm.hom) (TwoSquare.mk _ _ _ _ sa.hom)
    (TwoSquare.mk _ _ _ _ sG.inv) (TwoSquare.mk _ _ _ _ sH.inv)
    s₁D s₂D αD α'D γD δD hs₁ hs₂ hα hα' hγ hδ ?_ K
  intro X
  simpa only [TwoSquare.hComp_app, Category.assoc] using
    (Functor.comparisonCubeEquation_app sL sL' sG sH sm sa hwhole X).symm

end CategoryTheory
