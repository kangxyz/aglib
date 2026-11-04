/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ShiftedHom.Contraction

/-! Axiom guard for the original contraction. -/

/--
info: 'CategoryTheory.Adjunction.shiftedHomEquiv_contraction_value' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.shiftedHomEquiv_contraction_value
