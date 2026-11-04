/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.ShiftedAdjunct

/-! Axiom guard for the original finite-level shifted value. -/

open AlgebraicGeometry.Scheme.EtaleCohomology

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDerivedBaseChangeMapConstantRawShiftedValue'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleDerivedBaseChangeMapConstantRawShiftedValue
