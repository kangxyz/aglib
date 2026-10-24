/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactIsoCube
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HorizontalCube

/-!
# Exact whole cubes and their original derived mates

A whole natural-isomorphism cube of exact additive functors gives the literal
horizontal equation for four specified transformations on the installed
bounded-below derived functors. The supplied transformations are identified
with their native mates before taking any components. Scalar-forgetting
base-change comparisons consume this equation without an intermediate
specialization of the derived source cube.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open CategoryTheory.Functor
open TwoSquare

section MateEquation

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {R₁ : B ⥤ A} {R₂ : D ⥤ C} {R₁' : B' ⥤ A'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- The literal horizontal mate-cube equation for six specified transformations. -/
def HorizontalMateCubeEquation
    (b₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁') (b₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂')
    (μ : R₁ ⋙ G ⟶ H ⋙ R₂) (μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (γ : QA ⋙ G' ⟶ G ⋙ QC) (δ : QB ⋙ H' ⟶ H ⋙ QD) : Prop :=
  ∀ K, G'.map (b₁.app K) ≫ μ'.app (QB.obj K) ≫ R₂'.map (δ.app K) =
    γ.app (R₁.obj K) ≫ QC.map (μ.app K) ≫ b₂.app (H.obj K)

end MateEquation

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
  [EnoughInjectives D']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : C' ⥤ D'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [L₁'.Additive] [R₁'.Additive] [L₂'.Additive] [R₂'.Additive]
  [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
  [QA.Additive] [QB.Additive] [QC.Additive] [QD.Additive]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  [L₁'.PreservesHomology] [L₂'.PreservesHomology]
  [G.PreservesHomology] [H.PreservesHomology]
  [G'.PreservesHomology] [H'.PreservesHomology]
  [QA.PreservesHomology] [QB.PreservesHomology]
  [QC.PreservesHomology] [QD.PreservesHomology]

/-- A whole source cube and its six exact-comparison witnesses give the literal
cube equation for four specified native derived mates. Right adjoints need not
be exact, and no derived base-change map is assumed invertible. -/
theorem rightDerivedFunctorPlus_mateCube_of_whole
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
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
    (b₁ : R₁.rightDerivedFunctorPlus ⋙ QA.rightDerivedFunctorPlus ⟶
      QB.rightDerivedFunctorPlus ⋙ R₁'.rightDerivedFunctorPlus)
    (b₂ : R₂.rightDerivedFunctorPlus ⋙ QC.rightDerivedFunctorPlus ⟶
      QD.rightDerivedFunctorPlus ⋙ R₂'.rightDerivedFunctorPlus)
    (μ : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
      H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)
    (μ' : R₁'.rightDerivedFunctorPlus ⋙ G'.rightDerivedFunctorPlus ⟶
      H'.rightDerivedFunctorPlus ⋙ R₂'.rightDerivedFunctorPlus)
    (hb₁ : (mateEquiv adj₁.rightDerivedFunctorPlus adj₁'.rightDerivedFunctorPlus
      s₁D).natTrans = b₁)
    (hb₂ : (mateEquiv adj₂.rightDerivedFunctorPlus adj₂'.rightDerivedFunctorPlus
      s₂D).natTrans = b₂)
    (hμ : (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus
      αD).natTrans = μ)
    (hμ' : (mateEquiv adj₁'.rightDerivedFunctorPlus adj₂'.rightDerivedFunctorPlus
      α'D).natTrans = μ') :
    HorizontalMateCubeEquation b₁ b₂ μ μ' γD.natTrans δD.natTrans := by
  subst b₁ b₂ μ μ'
  intro K
  exact mateEquiv_horizontal_cube adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus
    adj₁'.rightDerivedFunctorPlus adj₂'.rightDerivedFunctorPlus
    s₁D s₂D αD α'D γD.natTrans δD.natTrans
    (rightDerivedFunctorPlus_exactHorizontalCube_of_whole
      sL sL' sG sH sm sa s₁D s₂D αD α'D γD δD
      hs₁ hs₂ hα hα' hγ hδ hwhole) K

end CategoryTheory
