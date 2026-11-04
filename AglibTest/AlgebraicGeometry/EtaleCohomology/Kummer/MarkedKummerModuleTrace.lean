/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.MarkedKummerModuleTrace

/-! Axiom guard for the original comparison. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummer_module_trace_boundary_roots'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummer_module_trace_boundary_roots
