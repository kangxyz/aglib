/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangePasting
public import Aglib.CategoryTheory.NatTrans.OverComparisonEquation
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementDirectImage

/-! # Original exchange pasting normalized by actual structural triangles -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wC wD wS wC' wD' wS'

variable (Λ : Type (u + 1)) [Ring Λ]
  {C D S C' D' S' : Scheme.{u}}
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]
  [HasDerivedCategory.{wD'} (ModuleSheaf D' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]

/-- Original vertical exchange pasting in the structural-triangle normalization.
No properness or invertibility of any exchange map is used. -/
theorem moduleUnboundedDerivedBaseChangeMap_over_comp
    (pC : C ⟶ S) (pD : D ⟶ S) (a : C ⟶ D) (ha : a ≫ pD = pC)
    (pC' : C' ⟶ S') (pD' : D' ⟶ S') (a' : C' ⟶ D') (ha' : a' ≫ pD' = pC')
    (b : S' ⟶ S) (qC : C' ⟶ C) (qD : D' ⟶ D)
    (hC : pC' ≫ b = qC ≫ pC) (hD : pD' ≫ b = qD ≫ pD)
    (hA : a' ≫ qD = qC ≫ a) (M : DerivedCategory (ModuleSheaf C Λ)) :
    (moduleUnboundedDerivedInverseImage Λ b).map
        ((moduleUnboundedDerivedDirectImageOverIso Λ pC pD a ha).hom.app M) ≫
      (moduleUnboundedDerivedBaseChangeMap Λ pC pC' b qC hC).app M ≫
      (moduleUnboundedDerivedDirectImageOverIso Λ pC' pD' a' ha').inv.app
        ((moduleUnboundedDerivedInverseImage Λ qC).obj M) =
    (moduleUnboundedDerivedBaseChangeMap Λ pD pD' b qD hD).app
        ((moduleUnboundedDerivedDirectImage Λ a).obj M) ≫
      (moduleUnboundedDerivedDirectImage Λ pD').map
        ((moduleUnboundedDerivedBaseChangeMap Λ a a' qD qC hA).app M) := by
  subst pC
  subst pC'
  have h := overComparisonBaseChangeEquation_of_vertical_pasting
    (moduleUnboundedDerivedDirectImageCompIso Λ pD a)
    (moduleUnboundedDerivedDirectImageCompIso Λ pD' a')
    (moduleUnboundedDerivedBaseChangeMap Λ (a ≫ pD) (a' ≫ pD') b qC hC)
    (moduleUnboundedDerivedBaseChangeMap Λ pD pD' b qD hD)
    (moduleUnboundedDerivedBaseChangeMap Λ a a' qD qC hA)
    (moduleUnboundedDerivedBaseChangeMap_vComp Λ pD a pD' a' b qD qC hD hA hC)
  simpa only [OverComparisonBaseChangeEquation, moduleUnboundedDerivedDirectImageOverIso,
    eqToIso_refl, Iso.trans_refl] using h M

/-- The whole equation retains the previously proved original component law. -/
theorem moduleUnboundedDerivedBaseChangeMap_over_comp_equation
    (pC : C ⟶ S) (pD : D ⟶ S) (a : C ⟶ D) (ha : a ≫ pD = pC)
    (pC' : C' ⟶ S') (pD' : D' ⟶ S') (a' : C' ⟶ D') (ha' : a' ≫ pD' = pC')
    (b : S' ⟶ S) (qC : C' ⟶ C) (qD : D' ⟶ D)
    (hC : pC' ≫ b = qC ≫ pC) (hD : pD' ≫ b = qD ≫ pD)
    (hA : a' ≫ qD = qC ≫ a) :
    OverComparisonBaseChangeEquation
      (moduleUnboundedDerivedDirectImageOverIso Λ pC pD a ha)
      (moduleUnboundedDerivedDirectImageOverIso Λ pC' pD' a' ha')
      (moduleUnboundedDerivedBaseChangeMap Λ pC pC' b qC hC)
      (moduleUnboundedDerivedBaseChangeMap Λ pD pD' b qD hD)
      (moduleUnboundedDerivedBaseChangeMap Λ a a' qD qC hA) :=
  moduleUnboundedDerivedBaseChangeMap_over_comp Λ pC pD a ha pC' pD' a' ha' b qC qD hC hD hA


end AlgebraicGeometry.Scheme.EtaleCohomology
