/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedRestrictionTrace

/-! Axiom guards for the original comparison. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummerH1Map_comp_inclusion'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummerH1Map_comp_inclusion

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummerH1Map_value_of_mapped'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummerH1Map_value_of_mapped

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummer_trace_boundary'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.markedKummer_trace_boundary
