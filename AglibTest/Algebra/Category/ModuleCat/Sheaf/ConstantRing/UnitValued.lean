/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnitValued

/-! # Original module-valued constant-unit map axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_underlying' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_underlying

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_app

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_isLocallySurjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_isLocallySurjective

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_isLocallyInjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleUnitConstantLinearMap_isLocallyInjective
