/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.SingleAdjunct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.Shift
public import Aglib.CategoryTheory.Shift.AdjunctValue

/-! Shifted values of the original module exchange. -/

open CategoryTheory

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wS wX wS' wX'

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

section Ring

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]

local notation "A" => DerivedCategory.Plus (ModuleSheaf S Λ)
local notation "B" => DerivedCategory.Plus (ModuleSheaf X Λ)
local notation "C" => DerivedCategory.Plus (ModuleSheaf S' Λ)
local notation "D" => DerivedCategory.Plus (ModuleSheaf X' Λ)
local notation "L₁" => moduleDerivedInverseImage Λ f
local notation "L₂" => moduleDerivedInverseImage Λ f'
local notation "R₂" => moduleDerivedDirectImage Λ f'
local notation "U" => moduleDerivedInverseImage Λ g
local notation "V" => moduleDerivedInverseImage Λ g'
local notation "adj₁" => moduleDerivedAdjunction Λ f
local notation "adj₂" => moduleDerivedAdjunction Λ f'

/-- Naturality transports the original shifted arrow through the original
module exchange from the specified unit adjunct. -/
abbrev moduleDerivedBaseChangeMapRawShiftedValue
    {I : A} {J K : B} {I' : C} {J' K' : D}
    (e : (L₁).obj I ≅ J) (e' : (L₂).obj I' ≅ J')
    (u : (U).obj I ≅ I') (v : (V).obj J ≅ J') (t : (V).obj K ≅ K')
    (h₀ : UnitAdjunctValue adj₁ adj₂ (moduleDerivedBaseChangeMap Λ f f' g g' h) e e' u v)
    {q : ℤ} (x : ShiftedHom J K q) :=
  let β := moduleDerivedBaseChangeMap Λ f f' g g' h
  let : NatTrans.CommShift β ℤ := moduleDerivedBaseChangeMap_commShift Λ f f' g g' h
  shiftedMateValue_of_unitAdjunct adj₁ adj₂ β e e' u v t h₀
    x (v.inv ≫ x.map (V) ≫ t.hom⟦q⟧') rfl

end Ring

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (n : ℕ)
  [HasDerivedCategory.{wS} (ModuleSheaf S (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' (ULift.{u + 1} (ZMod n)))]

/-- The original finite-level exchange on a shifted map between the original units. -/
abbrev moduleDerivedBaseChangeMapConstantRawShiftedValue {q : ℤ}
    (x :
      let Λ := ULift.{u + 1} (ZMod n)
      let J := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleUnit X Λ)
      ShiftedHom J J q) :=
  let Λ := ULift.{u + 1} (ZMod n)
  let e := (moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso f n)
  let e' := (moduleInverseImage f' Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso f' n)
  let u := (moduleInverseImage g Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso g n)
  let v := (moduleInverseImage g' Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso g' n)
  moduleDerivedBaseChangeMapRawShiftedValue Λ f f' g g' h e e' u v v
    (moduleDerivedBaseChangeMapConstantUnitAdjunct f f' g g' h n) x

end AlgebraicGeometry.Scheme.EtaleCohomology
