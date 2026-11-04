/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.DerivedAdjoint

open AlgebraicGeometry.Scheme.EtaleCohomology

/-! Native axiom guards for the original derived-adjoint comparison. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.cohomologyOriginalDerivedAdjunct_h1_value'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyOriginalDerivedAdjunct_h1_value

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.cohomologyOriginalDerivedAdjunct_h1_map'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyOriginalDerivedAdjunct_h1_map
