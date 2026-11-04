/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RepresentedCharacterPullback

/-! Axiom guard for the original comparison. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsH1Pullback_representedCharacter'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsH1Pullback_representedCharacter
