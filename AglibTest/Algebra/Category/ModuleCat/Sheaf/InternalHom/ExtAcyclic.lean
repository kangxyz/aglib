/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.ExtAcyclic

/-!
# Original internal-Hom provider axiom guards

Every public declaration retains the standard three-axiom predicate.
-/

/-- info: 'SheafOfModules.InternalHom.ext_subsingleton_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.ext_subsingleton_of_injective

/-- info: 'SheafOfModules.InternalHom.extZeroCohomologyAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.extZeroCohomologyAddEquiv

/-- info: 'SheafOfModules.InternalHom.extZeroCohomologyAddEquiv_mk₀' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.extZeroCohomologyAddEquiv_mk₀
