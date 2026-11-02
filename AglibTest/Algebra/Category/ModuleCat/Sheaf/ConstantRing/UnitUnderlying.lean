/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnitUnderlying

/-!
# Generic provider tests

These in-package checks retain independent universes and the approved axiom boundary
for every new public declaration in the corresponding provider.
-/

@[expose] public noncomputable section

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnit

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_whiskerRight_forget' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_whiskerRight_forget

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_isLocallyInjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_isLocallyInjective

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_isLocallySurjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_isLocallySurjective

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_presheafToSheaf_map_isIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantMap_presheafToSheaf_map_isIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitUnderlyingIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitUnderlyingIso
