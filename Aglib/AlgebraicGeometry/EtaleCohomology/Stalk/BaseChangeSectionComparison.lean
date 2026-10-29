/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SectionComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartRelative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductBaseChangeMap

/-! # The whole original section square on a base-changed chart

Four original higher exchanges and the two original inverse-image comparisons
give one square of section transformations. The original eight derived models
remain independent. Coefficient components are taken only after whole pasting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u dX dS dX' dS' dZU dU dZV dV

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [hDX : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hDS : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hDX' : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [hDS' : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (U : S.Etale)

/-- The actual original unit and higher-exchange section family. -/
def fibreProductBaseChangeSectionNatTrans (q : ℕ) :
    higherDirectImage f q ⋙
        (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) ⟶
      (inverseImage g' ⋙ higherDirectImage f' q) ⋙
        (sheafSections S'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op ((siteBaseChange g).obj U)) :=
  Continuity.unitSectionComparison g U (higherDirectImage f q)
    (inverseImage g' ⋙ higherDirectImage f' q)
    (@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q)

/-- The whole family has exactly the original raw unit and exchange components. -/
theorem fibreProductBaseChangeSectionNatTrans_app
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) :
    (fibreProductBaseChangeSectionNatTrans f f' g g' h U q).app F =
      ((inverseImageAdjunction g).unit.app ((higherDirectImage f q).obj F)).hom.app (op U) ≫
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
          hDX hDS hDX' hDS' f f' g g' h q).app F).hom.app
          (op ((siteBaseChange g).obj U)) :=
  Continuity.unitSectionComparison_app g U (higherDirectImage f q)
    (inverseImage g' ⋙ higherDirectImage f' q)
    (@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q) F

section ChartSquare

variable
  [hDZU : HasDerivedCategory.{dZU} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hDU : HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]
  [hDZV : HasDerivedCategory.{dZV}
    (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
  [hDV : HasDerivedCategory.{dV}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange g).obj U).left)]
  (q : ℕ)

-- These local abbreviations contain projections and explicit model universes.
set_option quotPrecheck false

local notation "V" => (siteBaseChange g).obj U
local notation "fU" => pullback.fst U.hom f
local notation "fV" => pullback.fst (V).hom f'
local notation "piU" => pullback.snd U.hom f
local notation "piV" => pullback.snd (V).hom f'
local notation "b" => pullback.fst U.hom g
local notation "r" => fibreProductBaseChangeMap f f' g g' h U
local notation "hR" => (fibreProductBaseChangeMap_fst f f' g g' h U).symm
local notation "hr" => (fibreProductBaseChangeMap_snd f f' g g' h U).symm
local notation "P" => higherDirectImage f q
local notation "P'" => higherDirectImage f' q
local notation "PU" => higherDirectImage fU q
local notation "PV" => higherDirectImage fV q
local notation "β" => (@higherBaseChangeMapFromDerived X S X' S'
  hDX hDS hDX' hDS' f f' g g' h q)
local notation "βU" => (@higherBaseChangeMapFromDerived
  X S (pullback U.hom f) U.left hDX hDS hDZU hDU
  f fU U.hom piU pullback.condition q)
local notation "βV" => (@higherBaseChangeMapFromDerived
  X' S' (pullback (V).hom f') (V).left hDX' hDS' hDZV hDV
  f' fV (V).hom piV pullback.condition q)
local notation "βR" => (@higherBaseChangeMapFromDerived
  (pullback U.hom f) U.left (pullback (V).hom f') (V).left hDZU hDU hDZV hDV
  fU fV b r hR q)
local notation "δS" => (inverseImageSquareIso U.hom (V).hom g b pullback.condition.symm).inv
local notation "δX" => (inverseImageSquareIso piU piV g' r hr).inv
local notation "ρ" =>
  ((TwoSquare.mk (inverseImage piU) (inverseImage g') (inverseImage r) (inverseImage piV) δX).hComp
    (TwoSquare.mk PU (inverseImage r) (inverseImage b) PV βR)).natTrans
local notation "βVhat" => (Functor.associator (inverseImage g') P' (inverseImage (V).hom)).hom ≫
  Functor.whiskerLeft (inverseImage g') βV

/-- Whole original exchange gives the square of the actual section families. -/
theorem higherBaseChangeMap_sectionChart_commSq :
    CommSq (fibreProductBaseChangeSectionNatTrans f f' g g' h U q)
      (Continuity.chartSectionComparison U P (inverseImage piU ⋙ PU) βU)
      (Continuity.chartSectionComparison V (inverseImage g' ⋙ P')
        (inverseImage g' ⋙ (inverseImage piV ⋙ PV)) βVhat)
      (Functor.comparisonPasting (globalSectionsPullbackNatTrans b) ρ) := by
  apply Continuity.sectionComparison_commSq
  exact Functor.comparisonPasting_coefficient_eq_of_twoSquare
    (TwoSquare.mk P (inverseImage g') (inverseImage g) P' β)
    (TwoSquare.mk P (inverseImage piU) (inverseImage U.hom) PU βU)
    (TwoSquare.mk P' (inverseImage piV) (inverseImage (V).hom) PV βV)
    (TwoSquare.mk PU (inverseImage r) (inverseImage b) PV βR)
    (TwoSquare.mk (inverseImage U.hom) (inverseImage g) (inverseImage b)
      (inverseImage (V).hom) δS)
    (TwoSquare.mk (inverseImage piU) (inverseImage g') (inverseImage r) (inverseImage piV) δX)
    (@higherBaseChangeMapFromDerived_chartRelative_square_whole.{u,
      dX, dS, dX', dS', dZU, dU, dZV, dV}
      X S X' S' (pullback U.hom f) U.left (pullback (V).hom f') (V).left
      hDX hDS hDX' hDS' hDZU hDU hDZV hDV f f' g g' h fU fV U.hom (V).hom
      piU piV b r pullback.condition pullback.condition pullback.condition.symm hr hR q)

/-- Evaluate the generic whole square at a coefficient, retaining its original chart factors. -/
theorem higherBaseChangeMap_sectionChart_square_app (F : AbelianSheaf.{u, u + 1} X) :
    (fibreProductBaseChangeSectionNatTrans f f' g g' h U q).app F ≫
        (Continuity.chartSectionComparison V P' (inverseImage piV ⋙ PV) βV).app
          ((inverseImage g').obj F) =
      (Continuity.chartSectionComparison U P (inverseImage piU ⋙ PU) βU).app F ≫
        globalSectionsPullback b ((PU).obj ((inverseImage piU).obj F)) ≫
        (globalSections (V).left).map
          ((βR).app ((inverseImage piU).obj F) ≫ (PV).map ((δX).app F)) :=
  Functor.comparisonPasting_twoSquare_app
    (Continuity.unitSectionNatTrans g (𝟙 V)) (globalSectionsPullbackNatTrans b)
    (Continuity.pullbackSectionsEtaleEvaluationNatIso U)
    (Continuity.pullbackSectionsEtaleEvaluationNatIso V)
    (TwoSquare.mk P (inverseImage g') (inverseImage g) P' β)
    (TwoSquare.mk P (inverseImage piU) (inverseImage U.hom) PU βU)
    (TwoSquare.mk P' (inverseImage piV) (inverseImage (V).hom) PV βV)
    (TwoSquare.mk PU (inverseImage r) (inverseImage b) PV βR)
    (TwoSquare.mk (inverseImage U.hom) (inverseImage g) (inverseImage b)
      (inverseImage (V).hom) δS)
    (TwoSquare.mk (inverseImage piU) (inverseImage g') (inverseImage r) (inverseImage piV) δX)
    (Continuity.unitSectionNatTrans_baseChangeChart_pasting g U)
    (@higherBaseChangeMapFromDerived_chartRelative_square_whole.{u,
      dX, dS, dX', dS', dZU, dU, dZV, dV}
      X S X' S' (pullback U.hom f) U.left (pullback (V).hom f') (V).left
      hDX hDS hDX' hDS' hDZU hDU hDZV hDV f f' g g' h fU fV U.hom (V).hom
      piU piV b r pullback.condition pullback.condition pullback.condition.symm hr hR q) F

end ChartSquare

end AlgebraicGeometry.Scheme.EtaleCohomology
