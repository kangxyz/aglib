/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TraceTransport

/-! Approved-axiom guards for the retained original declarations. -/

/--
info: 'CategoryTheory.existsUnique_originalTrace_classRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.existsUnique_originalTrace_classRestriction

/--
info: 'CategoryTheory.OriginalClassTraceRestrictionValue.normalized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.OriginalClassTraceRestrictionValue.normalized

/--
info: 'CategoryTheory.existsUnique_originalTrace_normalized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.existsUnique_originalTrace_normalized

/--
info: 'CategoryTheory.ShiftedHom.exists_originalShiftedTrace_normalized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.ShiftedHom.exists_originalShiftedTrace_normalized
