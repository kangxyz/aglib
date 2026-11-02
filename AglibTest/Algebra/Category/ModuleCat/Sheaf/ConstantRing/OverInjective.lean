/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.OverInjective

/-!
# Original internal-Hom provider axiom guards

Every public declaration retains the standard three-axiom predicate.
-/

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleDirectImage_over_preservesInjectiveObjects' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleDirectImage_over_preservesInjectiveObjects

/-- info: 'ModuleCat.Sheaf.ConstantRing.overFunctor_preservesInjectiveObjects' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overFunctor_preservesInjectiveObjects
