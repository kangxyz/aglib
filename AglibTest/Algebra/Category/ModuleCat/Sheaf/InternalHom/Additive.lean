/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Additive

/-!
# Original internal-Hom provider axiom guards

The native provider retains its actual maps and conditions. These in-package
checks guard every new public declaration against nonstandard axioms.
-/

@[expose] public noncomputable section

/-- info: 'SheafOfModules.InternalHom.homFunctor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.homFunctor_additive

/-- info: 'SheafOfModules.InternalHom.precomposeNatTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.precomposeNatTrans

/-- info: 'SheafOfModules.InternalHom.precomposeNatTrans_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.precomposeNatTrans_app

/-- info: 'SheafOfModules.InternalHom.precomposeNatTrans_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.precomposeNatTrans_id

/-- info: 'SheafOfModules.InternalHom.precomposeNatTrans_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.precomposeNatTrans_comp

/-- info: 'SheafOfModules.InternalHom.bifunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.bifunctor

/-- info: 'SheafOfModules.InternalHom.tensorRightFunctor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.tensorRightFunctor_additive

/-- info: 'SheafOfModules.InternalHom.homFunctor_isRightAdjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.homFunctor_isRightAdjoint

/-- info: 'SheafOfModules.InternalHom.homFunctor_preservesFiniteLimits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.homFunctor_preservesFiniteLimits
