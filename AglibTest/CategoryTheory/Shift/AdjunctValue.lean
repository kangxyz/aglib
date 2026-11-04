/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Shift.AdjunctValue

/-! Axiom guard for the original adjunction comparison. -/

open CategoryTheory

/--
info: 'CategoryTheory.shiftedMateValue_of_unitAdjunct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shiftedMateValue_of_unitAdjunct
