/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TraceExtZero

/-! Axiom guards for the original comparison. -/

/--
info: 'DerivedCategory.Plus.eq_mk₀_of_singleShiftTrace_homPlus'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DerivedCategory.Plus.eq_mk₀_of_singleShiftTrace_homPlus
