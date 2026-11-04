/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.ShiftedAdjunct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ConstantMap

/-! The original constant-unit pullback on original bounded-below Ext arrows. -/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open CategoryTheory CategoryTheory.Abelian
open Coefficients

universe u wX wZ wDX wDZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (n : ℕ)
  [HasDerivedCategory.{wDX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDZ} (ModuleSheaf Z (ULift.{u + 1} (ZMod n)))]

/-- The original inverse image carries the native derived unit to the native
unit on the target, through the original coefficient comparison. -/
@[no_expose]
def constantModuleDerivedUnitPullbackIso :
    let Λ := ULift.{u + 1} (ZMod n)
    (moduleDerivedInverseImage Λ f).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleUnit X Λ)) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj (moduleUnit Z Λ) := by
  let Λ := ULift.{u + 1} (ZMod n)
  exact (moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso f n)

/-- The constant unit comparison is the original degree-zero single transport. -/
theorem constantModuleDerivedUnitPullbackIso_eq :
    let Λ := ULift.{u + 1} (ZMod n)
    constantModuleDerivedUnitPullbackIso f n =
      (moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
        (moduleUnitInverseImageIso f n) := by
  unfold constantModuleDerivedUnitPullbackIso
  rfl

variable [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf Z (ULift.{u + 1} (ZMod n)))]

/-- The original constant-unit Ext pullback is the pullback of the same native
shifted arrow, with the original two unit transports. -/
theorem constantModuleExtPullback_homPlus (p : ℕ) (x : constantModuleExt.{u, wX} n X p) :
    (constantModuleExtPullback.{u, wX, wZ} n f p x).homPlus =
      (constantModuleDerivedUnitPullbackIso f n).inv ≫
        x.homPlus.map (moduleDerivedInverseImage (ULift.{u + 1} (ZMod n)) f) ≫
          (constantModuleDerivedUnitPullbackIso f n).hom⟦(p : ℤ)⟧' := by
  let Λ := ULift.{u + 1} (ZMod n)
  let F := moduleInverseImage f Λ
  let i := moduleUnitInverseImageIso f n
  rw [constantModuleExtPullback_apply]
  change (((Ext.mk₀ i.inv).comp (x.mapExactFunctor F) (zero_add p)).comp
    (Ext.mk₀ i.hom) (add_zero p)).homPlus = _
  exact F.mapExactFunctor_transport_homPlus i i p x

/-- The original pullback on Ext with the original single-unit comparison
displayed at both ends. -/
theorem constantModuleExtPullback_homPlus_singleTransport
    (p : ℕ) (x : constantModuleExt.{u, wX} n X p) :
    let Λ := ULift.{u + 1} (ZMod n)
    let F := moduleInverseImage f Λ
    let u := F.rightDerivedFunctorPlusSingleIsoOfIso 0 (moduleUnitInverseImageIso f n)
    (constantModuleExtPullback.{u, wX, wZ} n f p x).homPlus =
      u.inv ≫ x.homPlus.map (moduleDerivedInverseImage Λ f) ≫ u.hom⟦(p : ℤ)⟧' := by
  have h := constantModuleExtPullback_homPlus f n p x
  rw [constantModuleDerivedUnitPullbackIso_eq] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open CategoryTheory CategoryTheory.Abelian

universe u wS wX wS' wX' wEX wEX'

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (n : ℕ)
  [HasDerivedCategory.{wS} (ModuleSheaf S (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEX'} (ModuleSheaf X' (ULift.{u + 1} (ZMod n)))]

/-- The original shifted exchange carries the original pulled-back Ext class. -/
abbrev constantModuleExtPullbackShiftedMateValue
    (q : ℕ) (x : constantModuleExt.{u, wEX} n X q) :=
  let Λ := ULift.{u + 1} (ZMod n)
  let β := moduleDerivedBaseChangeMap Λ f f' g g' h
  let adj₁ := moduleDerivedAdjunction Λ f
  let adj₂ := moduleDerivedAdjunction Λ f'
  let r := moduleDerivedBaseChangeMapConstantRawShiftedValue f f' g g' h n x.homPlus
  let hy := constantModuleExtPullback_homPlus_singleTransport g' n q x
  ShiftedMateValue.target_eq adj₁ adj₂ β r hy

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
