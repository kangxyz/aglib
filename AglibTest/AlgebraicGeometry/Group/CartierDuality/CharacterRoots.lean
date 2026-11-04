/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.CharacterRoots

/-! Axiom guard for the original root character equivalence. -/

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.characterRootsEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.CartierDuality.characterRootsEquiv
