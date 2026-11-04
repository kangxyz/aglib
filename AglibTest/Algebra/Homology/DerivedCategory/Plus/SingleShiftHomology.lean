/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleShiftHomology

/-! Axiom guard for the original shifted single homology comparison. -/

/--
info: 'DerivedCategory.Plus.shiftedSingleHomologyOne'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DerivedCategory.Plus.shiftedSingleHomologyOne
