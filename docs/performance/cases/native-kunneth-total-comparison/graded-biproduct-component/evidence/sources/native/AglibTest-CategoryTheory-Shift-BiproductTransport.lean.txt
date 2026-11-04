/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Shift.BiproductTransport

/-! Axiom guard for the original graded biproduct transport. -/

open CategoryTheory

/--
info: 'CategoryTheory.regradedComponent_of_shiftedMateValue_biproduct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms regradedComponent_of_shiftedMateValue_biproduct
