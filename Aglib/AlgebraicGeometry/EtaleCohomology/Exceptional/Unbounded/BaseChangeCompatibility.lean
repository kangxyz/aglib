/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnitComparisonNaturality
public import
  Aglib.CategoryTheory.NatTrans.ImageComparisonBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenRefinementCube
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeOverComparisonEquation
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperRefinementComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactifiedBaseChange
public import Aglib.CategoryTheory.Functor.ImageComparison

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
theorem moduleUnboundedDerivedProperRefinementComparison_baseChange :
    UnitComparisonNaturalityEquation
      (moduleUnboundedDerivedBaseChangeMap Λ h h' qD qC hh.w.symm)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ).hom
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ).hom
      (moduleUnboundedDerivedProperRefinementComparison jC jD h sq Λ)
      (moduleUnboundedDerivedProperRefinementComparison jC' jD' h' sq' Λ) :=
  unitComparisonNaturalityEquation_of_mate
    (moduleUnboundedDerivedAdjunction Λ h) (moduleUnboundedDerivedAdjunction Λ h')
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ h h' qD qC hh.w.symm).hom)
    (moduleUnboundedDerivedBaseChangeMap Λ h h' qD qC hh.w.symm) rfl
    (moduleUnboundedDerivedProperRefinementPullbackIso jC jD h sq Λ).hom
    (moduleUnboundedDerivedProperRefinementPullbackIso jC' jD' h' sq' Λ).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ).hom
    (moduleUnboundedDerivedProperRefinementComparison jC jD h sq Λ)
    (moduleUnboundedDerivedProperRefinementComparison jC' jD' h' sq' Λ)
    (moduleUnboundedDerivedProperRefinementComparison_app jC jD h sq Λ)
    (moduleUnboundedDerivedProperRefinementComparison_app jC' jD' h' sq' Λ)
    (moduleUnboundedDerivedOpenComparison_refinement_cube
      jC jD h sq jC' jD' h' sq' a qC qD hC hD hh Λ)

variable {S T : Scheme.{u}}
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

include hh in
/-- Naturality of the literal raw compactified exchange with respect to the
original refinement transitions, as an equality of whole transformations. -/
theorem moduleUnboundedCompactifiedBaseChangeMap_refinement_naturality
    (pC : C ⟶ S) (pD : D ⟶ S) (hp : h ≫ pD = pC)
    (pC' : C' ⟶ T) (pD' : D' ⟶ T) (hp' : h' ≫ pD' = pC')
    (b : T ⟶ S) (hpC : IsPullback qC pC' pC b)
    (hpD : IsPullback qD pD' pD b) :
    ImageComparisonBaseChangeEquation
      (moduleUnboundedDerivedProperRefinementComparison jC jD h sq Λ)
      (moduleUnboundedDerivedProperRefinementComparison jC' jD' h' sq' Λ)
      (moduleUnboundedDerivedDirectImageOverIso Λ pC pD h hp)
      (moduleUnboundedDerivedDirectImageOverIso Λ pC' pD' h' hp')
      (moduleUnboundedDerivedBaseChangeMap Λ pC pC' b qC hpC.w.symm)
      (moduleUnboundedDerivedBaseChangeMap Λ pD pD' b qD hpD.w.symm)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ) :=
  imageComparisonBaseChangeEquation_of_squares
    (moduleUnboundedDerivedProperRefinementComparison jC jD h sq Λ)
    (moduleUnboundedDerivedProperRefinementComparison jC' jD' h' sq' Λ)
    (moduleUnboundedDerivedDirectImageOverIso Λ pC pD h hp)
    (moduleUnboundedDerivedDirectImageOverIso Λ pC' pD' h' hp')
    (moduleUnboundedDerivedBaseChangeMap Λ pC pC' b qC hpC.w.symm)
    (moduleUnboundedDerivedBaseChangeMap Λ pD pD' b qD hpD.w.symm)
    (moduleUnboundedDerivedBaseChangeMap Λ h h' qD qC hh.w.symm)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ)
    (moduleUnboundedDerivedProperRefinementComparison_baseChange
      jC jD h sq jC' jD' h' sq' a qC qD hC hD hh Λ)
    (moduleUnboundedDerivedBaseChangeMap_over_comp_equation Λ pC pD h hp
      pC' pD' h' hp' b qC qD hpC.w.symm hpD.w.symm hh.w.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
