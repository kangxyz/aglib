/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ShiftedHom

/-! Axiom guards for the original shift comparison. -/

open CategoryTheory

/--
info: 'CategoryTheory.shiftedHomEquiv_of_mate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shiftedHomEquiv_of_mate
