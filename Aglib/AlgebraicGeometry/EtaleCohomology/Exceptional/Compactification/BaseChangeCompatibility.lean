/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnitComparisonNaturality
public import Aglib.CategoryTheory.NatTrans.ImageComparisonBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenRefinementCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeOverComparisonEquation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonAlgebra

/-!
# Original refinement comparisons commute with the raw exchange

The unit-comparison square is obtained from the actual open/inverse-image cube
by the abstract mate calculation. The structural-image square is the original
proper-exchange pasting law. Their abstract composition retains all original
maps; no chosen objectwise isomorphisms replace either comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wC wD wU' wC' wD' wS wT

variable {U C D U' C' D' : Scheme.{u}}
  (jC : U ⟶ C) (jD : U ⟶ D) (h : C ⟶ D)
  (sq : IsPullback jC (𝟙 U) h jD)
  (jC' : U' ⟶ C') (jD' : U' ⟶ D') (h' : C' ⟶ D')
  (sq' : IsPullback jC' (𝟙 U') h' jD')
  (a : U' ⟶ U) (qC : C' ⟶ C) (qD : D' ⟶ D)
  [IsOpenImmersion jC] [IsOpenImmersion jD]
  [IsOpenImmersion jC'] [IsOpenImmersion jD']
  (hC : IsPullback a jC' jC qC) (hD : IsPullback a jD' jD qD)
  (hh : IsPullback qC h' h qD)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]
  [HasDerivedCategory.{wD'} (ModuleSheaf D' Λ)]

/-- The original proper-refinement unit comparison commutes with the original
exchange and the original open Cartesian comparisons. -/
theorem moduleDerivedProperRefinementComparison_baseChange :
    UnitComparisonNaturalityEquation
      (moduleDerivedBaseChangeMap Λ h h' qD qC hh.w.symm)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ).hom
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ).hom
      (moduleDerivedProperRefinementComparison jC jD h sq Λ)
      (moduleDerivedProperRefinementComparison jC' jD' h' sq' Λ) :=
  unitComparisonNaturalityEquation_of_mate
    (moduleDerivedAdjunction Λ h) (moduleDerivedAdjunction Λ h')
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ h h' qD qC hh.w.symm).hom)
    (moduleDerivedBaseChangeMap Λ h h' qD qC hh.w.symm) rfl
    (moduleDerivedProperRefinementPullbackIso jC jD h sq Λ).hom
    (moduleDerivedProperRefinementPullbackIso jC' jD' h' sq' Λ).hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ).hom
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ).hom
    (moduleDerivedProperRefinementComparison jC jD h sq Λ)
    (moduleDerivedProperRefinementComparison jC' jD' h' sq' Λ)
    (moduleDerivedProperRefinementComparison_app jC jD h sq Λ)
    (moduleDerivedProperRefinementComparison_app jC' jD' h' sq' Λ)
    (moduleDerivedOpenComparison_refinement_cube
      jC jD h sq jC' jD' h' sq' a qC qD hC hD hh Λ)

variable {S T : Scheme.{u}}
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

include hh in
/-- Naturality of the literal raw compactified exchange with respect to the
original refinement transitions, as an equality of whole transformations. -/
theorem moduleCompactifiedBaseChangeMap_refinement_naturality
    (pC : C ⟶ S) (pD : D ⟶ S) (hp : h ≫ pD = pC)
    (pC' : C' ⟶ T) (pD' : D' ⟶ T) (hp' : h' ≫ pD' = pC')
    (b : T ⟶ S) (hpC : IsPullback qC pC' pC b)
    (hpD : IsPullback qD pD' pD b) :
    ImageComparisonBaseChangeEquation
      (moduleDerivedProperRefinementComparison jC jD h sq Λ)
      (moduleDerivedProperRefinementComparison jC' jD' h' sq' Λ)
      (moduleDerivedDirectImageOverIso Λ pC pD h hp)
      (moduleDerivedDirectImageOverIso Λ pC' pD' h' hp')
      (moduleDerivedBaseChangeMap Λ pC pC' b qC hpC.w.symm)
      (moduleDerivedBaseChangeMap Λ pD pD' b qD hpD.w.symm)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ) :=
  imageComparisonBaseChangeEquation_of_squares
    (moduleDerivedProperRefinementComparison jC jD h sq Λ)
    (moduleDerivedProperRefinementComparison jC' jD' h' sq' Λ)
    (moduleDerivedDirectImageOverIso Λ pC pD h hp)
    (moduleDerivedDirectImageOverIso Λ pC' pD' h' hp')
    (moduleDerivedBaseChangeMap Λ pC pC' b qC hpC.w.symm)
    (moduleDerivedBaseChangeMap Λ pD pD' b qD hpD.w.symm)
    (moduleDerivedBaseChangeMap Λ h h' qD qC hh.w.symm)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ)
    (moduleDerivedProperRefinementComparison_baseChange
      jC jD h sq jC' jD' h' sq' a qC qD hC hD hh Λ)
    (moduleDerivedBaseChangeMap_over_comp_equation Λ pC pD h hp
      pC' pD' h' hp' b qC qD hpC.w.symm hpD.w.symm hh.w.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
