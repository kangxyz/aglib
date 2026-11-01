/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactIsoCube
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.SpecifiedMateCube

/-! # A whole exact cube for four specified native unbounded mates

The original source cube and six exact-factor equations supply the actual
four-mate predicate directly. Right adjoints are the supplied native functors;
no exactness, geometric bound, or exchange-invertibility premise is imposed.
-/

@[expose] public noncomputable section


namespace CategoryTheory

open CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.TwoSquare

universe uA vA wA uB vB wB uC vC wC uD vD wD
  uA' vA' wA' uB' vB' wB' uC' vC' wC' uD' vD' wD'

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  {C' : Type uC'} [Category.{vC'} C'] [Abelian C'] [HasDerivedCategory.{wC'} C']
  {D' : Type uD'} [Category.{vD'} D'] [Abelian D'] [HasDerivedCategory.{wD'} D']
  {L₁ : A ⥤ B} {L₂ : C ⥤ D}
  {L₁' : A' ⥤ B'} {L₂' : C' ⥤ D'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  [L₁.Additive] [L₂.Additive]
  [L₁'.Additive] [L₂'.Additive]
  [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
  [QA.Additive] [QB.Additive] [QC.Additive] [QD.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits L₁'] [PreservesFiniteColimits L₁']
  [PreservesFiniteLimits L₂'] [PreservesFiniteColimits L₂']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits QA] [PreservesFiniteColimits QA]
  [PreservesFiniteLimits QB] [PreservesFiniteColimits QB]
  [PreservesFiniteLimits QC] [PreservesFiniteColimits QC]
  [PreservesFiniteLimits QD] [PreservesFiniteColimits QD]

variable {R₁D : DerivedCategory B ⥤ DerivedCategory A}
  {R₂D : DerivedCategory D ⥤ DerivedCategory C}
  {R₁'D : DerivedCategory B' ⥤ DerivedCategory A'}
  {R₂'D : DerivedCategory D' ⥤ DerivedCategory C'}

/-- A whole source cube and its six exact-comparison witnesses give the literal
cube equation for four specified native derived mates. Right adjoints need not
be exact, and no derived base-change map is assumed invertible. -/
theorem mapDerivedCategory_mateCube_of_whole
    (adj₁ : L₁.mapDerivedCategory ⊣ R₁D) (adj₂ : L₂.mapDerivedCategory ⊣ R₂D)
    (adj₁' : L₁'.mapDerivedCategory ⊣ R₁'D) (adj₂' : L₂'.mapDerivedCategory ⊣ R₂'D)
    (sL : L₁ ⋙ QB ≅ QA ⋙ L₁') (sL' : L₂ ⋙ QD ≅ QC ⋙ L₂')
    (sG : G ⋙ QC ≅ QA ⋙ G') (sH : H ⋙ QD ≅ QB ⋙ H')
    (sm : G ⋙ L₂ ≅ L₁ ⋙ H) (sa : G' ⋙ L₂' ≅ L₁' ⋙ H')
    (s₁D : TwoSquare QA.mapDerivedCategory L₁.mapDerivedCategory
      L₁'.mapDerivedCategory QB.mapDerivedCategory)
    (s₂D : TwoSquare QC.mapDerivedCategory L₂.mapDerivedCategory
      L₂'.mapDerivedCategory QD.mapDerivedCategory)
    (αD : TwoSquare G.mapDerivedCategory L₁.mapDerivedCategory
      L₂.mapDerivedCategory H.mapDerivedCategory)
    (α'D : TwoSquare G'.mapDerivedCategory L₁'.mapDerivedCategory
      L₂'.mapDerivedCategory H'.mapDerivedCategory)
    (γD : TwoSquare QA.mapDerivedCategory G.mapDerivedCategory
      G'.mapDerivedCategory QC.mapDerivedCategory)
    (δD : TwoSquare QB.mapDerivedCategory H.mapDerivedCategory
      H'.mapDerivedCategory QD.mapDerivedCategory)
    (hs₁ : ∀ Z, ExactFactorSquareEquation L₁ QB QA L₁'
      (TwoSquare.mk _ _ _ _ sL.inv) s₁D Z)
    (hs₂ : ∀ Z, ExactFactorSquareEquation L₂ QD QC L₂'
      (TwoSquare.mk _ _ _ _ sL'.inv) s₂D Z)
    (hα : ∀ Z, ExactFactorSquareEquation L₁ H G L₂
      (TwoSquare.mk _ _ _ _ sm.hom) αD Z)
    (hα' : ∀ Z, ExactFactorSquareEquation L₁' H' G' L₂'
      (TwoSquare.mk _ _ _ _ sa.hom) α'D Z)
    (hγ : ∀ Z, ExactFactorSquareEquation G QC QA G'
      (TwoSquare.mk _ _ _ _ sG.inv) γD Z)
    (hδ : ∀ Z, ExactFactorSquareEquation H QD QB H'
      (TwoSquare.mk _ _ _ _ sH.inv) δD Z)
    (hwhole : Functor.ComparisonCubeEquation sL sL' sG sH sm sa)
    (b₁ : R₁D ⋙ QA.mapDerivedCategory ⟶
      QB.mapDerivedCategory ⋙ R₁'D)
    (b₂ : R₂D ⋙ QC.mapDerivedCategory ⟶
      QD.mapDerivedCategory ⋙ R₂'D)
    (μ : R₁D ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R₂D)
    (μ' : R₁'D ⋙ G'.mapDerivedCategory ⟶
      H'.mapDerivedCategory ⋙ R₂'D)
    (hb₁ : (mateEquiv adj₁ adj₁'
      s₁D).natTrans = b₁)
    (hb₂ : (mateEquiv adj₂ adj₂'
      s₂D).natTrans = b₂)
    (hμ : (mateEquiv adj₁ adj₂
      αD).natTrans = μ)
    (hμ' : (mateEquiv adj₁' adj₂'
      α'D).natTrans = μ') :
    HorizontalMateCubeEquation b₁ b₂ μ μ' γD.natTrans δD.natTrans := by
  subst b₁ b₂ μ μ'
  intro K
  exact mateEquiv_horizontal_cube adj₁ adj₂
    adj₁' adj₂'
    s₁D s₂D αD α'D γD.natTrans δD.natTrans
    (mapDerivedCategory_exactHorizontalCube_of_whole
      sL sL' sG sH sm sa s₁D s₂D αD α'D γD δD
      hs₁ hs₂ hα hα' hγ hδ hwhole) K

end CategoryTheory
