/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalTrace

/-! Axiom guard for the original diagonal trace evaluation. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.diagonalModuleKummerClass_trace_of_normalized'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diagonalModuleKummerClass_trace_of_normalized
