/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.Evaluation

/-! # Axiom guards for the original Cartier comparison laws -/

@[expose] public section

open AlgebraicGeometry.Scheme.Group.CartierDuality

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dual_point_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dual_point_ext

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dualGroupBaseChangeIso_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dualGroupBaseChangeIso_evaluation
