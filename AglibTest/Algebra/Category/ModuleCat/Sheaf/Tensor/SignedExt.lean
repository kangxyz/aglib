/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.SignedExt

/-! Axiom guards for the public declarations of this leaf. -/

/--
info: 'SheafOfModulesOfCommRing.ext_comp_tensorRightUnitExt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModulesOfCommRing.ext_comp_tensorRightUnitExt

/--
info: 'SheafOfModulesOfCommRing.ext_comp_tensorRightIsoUnitExt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModulesOfCommRing.ext_comp_tensorRightIsoUnitExt
