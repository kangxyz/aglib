/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TopTrace

/-! Axiom guard for the original shifted top trace evaluation. -/

open DerivedCategory.Plus

/--
info: 'DerivedCategory.Plus.shifted_topTrace_comp_eq_id_of_value' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shifted_topTrace_comp_eq_id_of_value
