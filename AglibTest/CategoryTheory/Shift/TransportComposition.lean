/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Shift.TransportComposition

/-! Axiom guard for the original comparison. -/

/--
info: 'CategoryTheory.ShiftedHom.map_comp_transport_of_values'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.ShiftedHom.map_comp_transport_of_values
