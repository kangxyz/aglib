/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.SupportFactorization

/-! Axiom guards for the original supported factorization. -/

open AlgebraicGeometry.Scheme.EtaleCohomology

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDerived_exists_comp_closedUnit_of_open_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleDerived_exists_comp_closedUnit_of_open_zero

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDerived_comp_eq_of_closed_eq_of_open_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleDerived_comp_eq_of_closed_eq_of_open_zero
