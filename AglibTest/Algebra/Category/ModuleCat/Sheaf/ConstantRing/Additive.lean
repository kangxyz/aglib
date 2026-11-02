/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive

/-! # Original whole coefficient/presheaf/complex comparison axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive
