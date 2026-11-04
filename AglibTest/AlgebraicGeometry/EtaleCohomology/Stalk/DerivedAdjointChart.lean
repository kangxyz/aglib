/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.DerivedAdjointChart

open AlgebraicGeometry.Scheme.EtaleCohomology

/-! Native axiom guards for the original derived-adjoint comparison. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.cohomologyToHigherSections_terminalFibreProduct'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyToHigherSections_terminalFibreProduct

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.cohomologyOriginalDerivedAdjunct_terminalChart_value'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyOriginalDerivedAdjunct_terminalChart_value

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.cohomologyToHigherSections_terminalPullback'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyToHigherSections_terminalPullback

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.cohomologyOriginalDerivedAdjunct_terminalPullback_value'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyOriginalDerivedAdjunct_terminalPullback_value
