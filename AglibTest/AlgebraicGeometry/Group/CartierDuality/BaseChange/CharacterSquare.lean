/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.CharacterSquare

/-! Axiom boundary for the original Cartier character square. -/

open AlgebraicGeometry.Scheme.Group.CartierDuality

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dualGroupBaseChangeOverIso_character_square'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dualGroupBaseChangeOverIso_character_square
