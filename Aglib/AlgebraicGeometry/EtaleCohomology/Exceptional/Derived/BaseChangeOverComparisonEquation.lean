/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.OverComparisonEquation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeOverComparison

/-! # Whole original exchange compatibility with structural triangles -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wC wD wS wC' wD' wT

variable (Λ : Type (u + 1)) [Ring Λ]
  {C D S C' D' T : Scheme.{u}}
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]
  [HasDerivedCategory.{wD'} (ModuleSheaf D' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- The whole equation retains the previously proved original component law. -/
theorem moduleDerivedBaseChangeMap_over_comp_equation
    (pC : C ⟶ S) (pD : D ⟶ S) (a : C ⟶ D) (ha : a ≫ pD = pC)
    (pC' : C' ⟶ T) (pD' : D' ⟶ T) (a' : C' ⟶ D') (ha' : a' ≫ pD' = pC')
    (b : T ⟶ S) (qC : C' ⟶ C) (qD : D' ⟶ D)
    (hC : pC' ≫ b = qC ≫ pC) (hD : pD' ≫ b = qD ≫ pD)
    (hA : a' ≫ qD = qC ≫ a) :
    OverComparisonBaseChangeEquation
      (moduleDerivedDirectImageOverIso Λ pC pD a ha)
      (moduleDerivedDirectImageOverIso Λ pC' pD' a' ha')
      (moduleDerivedBaseChangeMap Λ pC pC' b qC hC)
      (moduleDerivedBaseChangeMap Λ pD pD' b qD hD)
      (moduleDerivedBaseChangeMap Λ a a' qD qC hA) :=
  moduleDerivedBaseChangeMap_over_comp Λ pC pD a ha pC' pD' a' ha' b qC qD hC hD hA

end AlgebraicGeometry.Scheme.EtaleCohomology
