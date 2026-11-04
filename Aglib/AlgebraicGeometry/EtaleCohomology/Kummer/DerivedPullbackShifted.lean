/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.ShiftedAdjunct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback

/-! Original shifted-mate equation for roots Ext pullback. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wS wX wS' wX' wEX wEX'
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
  [HasDerivedCategory.{wS} (ModuleSheaf S (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEX'} (ModuleSheaf X' (ULift.{u + 1} (ZMod n)))]

/-- The same module exchange carries any original roots Ext class to its actual pullback. -/
abbrev moduleRootsUnitExtPullbackShiftedMateValue (q : ℕ)
    (x : Ext.{wEX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q) :=
  let Λ := ULift.{u + 1} (ZMod n)
  let β := moduleDerivedBaseChangeMap Λ f f' g g' h
  let adj₁ := moduleDerivedAdjunction Λ f
  let adj₂ := moduleDerivedAdjunction Λ f'
  let e := (moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso f n)
  let e' := (moduleInverseImage f' Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso f' n)
  let u := (moduleInverseImage g Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso g n)
  let v := (moduleInverseImage g' Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso g' n)
  let t := moduleRootsDerivedSinglePullbackIso g' n hn hinv
  let h₀ := moduleDerivedBaseChangeMapConstantUnitAdjunct f f' g g' h n
  let raw := moduleDerivedBaseChangeMapRawShiftedValue Λ f f' g g' h e e' u v t h₀ x.homPlus
  let target := ShiftedMateValue.target_eq adj₁ adj₂ β raw
    (moduleRootsUnitExtPullback_homPlus g' n hn hinv q x)
  ShiftedMateValue.transport adj₁ adj₂ β target
    (constantModuleDerivedUnitPullbackIso_eq f n)
    (constantModuleDerivedUnitPullbackIso_eq f' n)
    (constantModuleDerivedUnitPullbackIso_eq g n) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
