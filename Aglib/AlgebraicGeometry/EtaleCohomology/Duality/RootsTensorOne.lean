/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Stability
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.SignedExt
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsDerivedEvaluation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ConstantMap
public import Aglib.AlgebraicGeometry.SchemeOverField

/-! The original signed degree-one action on the roots coefficient. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModulesOfCommRing

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients Scheme.OverField

universe u wX wZ wU wAX wAZ wAU wDX wDZ wDU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

set_option hygiene false in
local notation "ℛ" Z => ModuleCat.Sheaf.ConstantRing.commutativeSheaf
  (Scheme.smallEtaleTopology Z) Λ

/-- The monoidal comparison for the original module localization. -/
local instance originalModuleTensorLocalization (Z : Scheme.{u}) :
    (presheafLocalIso (ℛ Z)).IsMonoidal :=
  presheafLocalIso_isMonoidal.{u + 1, u, 0} (ℛ Z)

section TensorAction

variable {Z : Scheme.{u}} (p : Z ⟶ Base k) [hExt : HasExt.{wZ} (ModuleSheaf Z Λ)]

/-- The original Ext universe for modules over the same coefficient ring. -/
local instance rootsTensorHasExt :
    HasExt.{wZ} (SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z)) := hExt

/-- Tensor the original degree-one constant class by the original roots module. -/
abbrev moduleRootsExtOneTensor (x : constantModuleExt.{u, wZ} n Z 1) :=
  letI : PreservesFiniteLimits
      (tensorRight (C := SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z))
        (moduleRootsOfUnity Z n)) :=
    moduleRootsTensorRight_preservesFiniteLimits k n hn hu p
  letI : PreservesFiniteColimits
      (tensorRight (C := SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z))
        (moduleRootsOfUnity Z n)) :=
    moduleRootsTensorRight_preservesFiniteColimits k n hn hu p
  Ext.tensorRightIsoUnitExt (D := SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z))
    (moduleRootsOfUnity Z n)
    (SheafOfModules.liftedUnitIso (constantRing Z Λ)) x

/-- The original root-tensor action moves a unit extension past a degree-two class. -/
theorem comp_rootsExtTwo_eq_tensor (x : constantModuleExt.{u, wZ} n Z 1)
    (c : Ext.{wZ} (moduleUnit Z Λ) (moduleRootsOfUnity Z n) 2) :
    x.comp c (rfl : 1 + 2 = 3) =
      c.comp (moduleRootsExtOneTensor n hn hu p x) (rfl : 2 + 1 = 3) := by
  let : PreservesFiniteLimits
      (tensorRight (C := SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z))
        (moduleRootsOfUnity Z n)) :=
    moduleRootsTensorRight_preservesFiniteLimits k n hn hu p
  let : PreservesFiniteColimits
      (tensorRight (C := SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z))
        (moduleRootsOfUnity Z n)) :=
    moduleRootsTensorRight_preservesFiniteColimits k n hn hu p
  have h := ext_comp_tensorRightIsoUnitExt.{0, u + 1, u, wZ} (ℛ Z) (moduleRootsOfUnity Z n)
    (SheafOfModules.liftedUnitIso (constantRing Z Λ)) x c
  let y := c.comp (moduleRootsExtOneTensor n hn hu p x) (rfl : 2 + 1 = 3)
  have hs : (-1 : ℤ) ^ (2 : ℕ) = 1 := rfl
  have hv : ((-1 : ℤ) ^ (2 : ℕ)) • y = y :=
    (congrArg (fun a : ℤ => a • y) hs).trans (one_smul ℤ y)
  exact h.trans hv

/-- The original root-tensor action moves a unit extension past a degree-one class
with a negative sign. -/
theorem comp_rootsExtOne_eq_neg_tensor (x : constantModuleExt.{u, wZ} n Z 1)
    (c : Ext.{wZ} (moduleUnit Z Λ) (moduleRootsOfUnity Z n) 1) :
    x.comp c (rfl : 1 + 1 = 2) =
      -(c.comp (moduleRootsExtOneTensor n hn hu p x) (rfl : 1 + 1 = 2)) := by
  let : PreservesFiniteLimits
      (tensorRight (C := SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z))
        (moduleRootsOfUnity Z n)) :=
    moduleRootsTensorRight_preservesFiniteLimits k n hn hu p
  let : PreservesFiniteColimits
      (tensorRight (C := SheafOfModulesOfCommRing.{u + 1, u + 1, u} (ℛ Z))
        (moduleRootsOfUnity Z n)) :=
    moduleRootsTensorRight_preservesFiniteColimits k n hn hu p
  have h := ext_comp_tensorRightIsoUnitExt.{0, u + 1, u, wZ} (ℛ Z) (moduleRootsOfUnity Z n)
    (SheafOfModules.liftedUnitIso (constantRing Z Λ)) x c
  let y := c.comp (moduleRootsExtOneTensor n hn hu p x) (rfl : 1 + 1 = 2)
  have hs : (-1 : ℤ) ^ (1 : ℕ) = -1 := rfl
  exact h.trans ((congrArg (fun d : ℤ => d • y) hs).trans (neg_one_zsmul y))

end TensorAction

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
