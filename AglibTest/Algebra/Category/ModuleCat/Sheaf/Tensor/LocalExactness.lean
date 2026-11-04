/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.LocalExactness

/-! Axiom guards for the public declarations of this leaf. -/

/--
info: 'SheafOfModulesOfCommRing.tensorFunctor_mono_f_of_unit_quotient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModulesOfCommRing.tensorFunctor_mono_f_of_unit_quotient

/--
info: 'SheafOfModulesOfCommRing.shortExact_tensorRight_of_unit_quotient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModulesOfCommRing.shortExact_tensorRight_of_unit_quotient
