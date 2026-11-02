/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.LiftedUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Original internal-Hom provider axiom guards

The native provider retains its actual maps and conditions. These in-package
checks guard every new public declaration against nonstandard axioms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe c h r e e'

/-- The selected lifted unit computes degree-zero Ext with two independent Ext universes. -/
example {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
    (R : Sheaf J CommRingCat.{max c h r})
    [HasSheafify J AddCommGrpCat.{max c h r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]
    [HasExt.{e} (SheafOfModulesOfCommRing R)]
    [HasExt.{e'} (SheafOfModulesOfCommRing R)] (M N : SheafOfModulesOfCommRing R) :
    Ext.{e} M N 0 ≃+
      Ext.{e'} (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (SheafOfModules.InternalHom.sheaf R M N) 0 :=
  by
    let E := (SheafOfModules.InternalHom.liftedUnitCoyonedaIso.{c, h, r}
      R M).symm.app N
    exact Ext.addEquiv₀.trans (E.addCommGroupIsoToAddEquiv.trans Ext.addEquiv₀.symm)

/-- info: 'SheafOfModules.liftedUnitIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.liftedUnitIso

/-- info: 'SheafOfModules.liftedUnitIso_hom_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.liftedUnitIso_hom_app

/-- info: 'SheafOfModules.liftedUnitIso_inv_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.liftedUnitIso_inv_app

/-- info: 'SheafOfModules.InternalHom.liftedUnitCoyonedaIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.liftedUnitCoyonedaIso

/-- info: 'SheafOfModules.InternalHom.liftedUnitCoyonedaIso_hom_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.liftedUnitCoyonedaIso_hom_app_apply
