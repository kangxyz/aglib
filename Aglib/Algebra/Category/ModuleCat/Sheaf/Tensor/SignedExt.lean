/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.LocalExactness
public import Aglib.Algebra.Homology.DerivedCategory.Ext.TensorUnitExt

/-! Signed Ext action of a unit self-extension for the native module-sheaf tensor. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w e

namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max v w u} RingCat.{max v w u})]
    (R : Sheaf J CommRingCat.{max v w u}) [HasSheafify J AddCommGrpCat.{max v w u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v w u}]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max v w u})]
    [(presheafLocalIso R).IsMonoidal] [HasExt.{e} (SheafOfModulesOfCommRing R)]

local notation "D" => SheafOfModulesOfCommRing R
local notation "𝒪" => 𝟙_ D

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Signed action of a degree-one unit extension on module-sheaf Ext. -/
theorem ext_comp_tensorRightUnitExt
    (M : SheafOfModulesOfCommRing R) [PreservesFiniteLimits (tensorRight M)]
    [PreservesFiniteColimits (tensorRight M)]
    (x : Ext.{e} 𝒪 𝒪 1) {q : ℕ} (c : Ext.{e} 𝒪 M q) :
    x.comp c rfl =
      ((-1 : ℤ) ^ q) • c.comp (Ext.tensorRightUnitExt M x) (Nat.add_comm q 1) :=
  Ext.comp_tensorRightUnitExt M
    (fun E N => shortExact_tensorRight_of_unit_quotient.{u, v, w} R
      E.toShortComplex E.shortExact (Iso.refl _) N) x c

/-- Signed action of a degree-one extension at a module sheaf identified with the unit. -/
theorem ext_comp_tensorRightIsoUnitExt
    (M : SheafOfModulesOfCommRing R) [PreservesFiniteLimits (tensorRight M)]
    [PreservesFiniteColimits (tensorRight M)]
    {U : SheafOfModulesOfCommRing R} (a : U ≅ 𝒪)
    (x : Ext.{e} U U 1) {q : ℕ} (c : Ext.{e} U M q) :
    x.comp c rfl =
      ((-1 : ℤ) ^ q) • c.comp (Ext.tensorRightIsoUnitExt M a x) (Nat.add_comm q 1) :=
  Ext.comp_tensorRightIsoUnitExt M
    (fun E N => shortExact_tensorRight_of_unit_quotient.{u, v, w} R
      E.toShortComplex E.shortExact (Iso.refl _) N) a x c

end SheafOfModulesOfCommRing
