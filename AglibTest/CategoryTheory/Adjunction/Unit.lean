/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Adjunction.Unit

/-! Axiom guards for bijectivity of a left adjoint on morphisms into an object where the unit is
invertible (`Aglib.CategoryTheory.Adjunction.Unit`). -/

@[expose] public section

/--
info: 'CategoryTheory.Adjunction.bijective_map_of_isIso_unit_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Adjunction.bijective_map_of_isIso_unit_app
