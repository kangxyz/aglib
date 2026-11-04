/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty.Group

/-! # Axiom guards for the original Cartier comparison laws -/

@[expose] public section

open AlgebraicGeometry.Scheme.Group.CartierDuality

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.evaluationPointUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evaluationPointUnit

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.evaluationPointUnit_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evaluationPointUnit_mul

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.characterOfPoint_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms characterOfPoint_mul

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.characterEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms characterEquiv_mul
