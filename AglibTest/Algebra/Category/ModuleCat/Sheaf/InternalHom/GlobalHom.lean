/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.GlobalHom

/-!
# Original internal-Hom provider axiom guards

The native provider retains its actual maps and conditions. These in-package
checks guard every new public declaration against nonstandard axioms.
-/

@[expose] public noncomputable section

/-- info: 'SheafOfModules.InternalHom.uncurry_precompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.uncurry_precompose

/-- info: 'SheafOfModules.InternalHom.unitHomAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitHomAddEquiv

/-- info: 'SheafOfModules.InternalHom.unitHomAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitHomAddEquiv_apply

/-- info: 'SheafOfModules.InternalHom.unitHomAddEquiv_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitHomAddEquiv_naturality

/-- info: 'SheafOfModules.InternalHom.unitCoyonedaIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitCoyonedaIso

/-- info: 'SheafOfModules.InternalHom.unitCoyonedaIso_hom_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitCoyonedaIso_hom_app_apply

/-- info: 'SheafOfModules.InternalHom.unitHomAddEquiv_precompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitHomAddEquiv_precompose

/-- info: 'SheafOfModules.InternalHom.unitCoyonedaIso_precompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.unitCoyonedaIso_precompose
