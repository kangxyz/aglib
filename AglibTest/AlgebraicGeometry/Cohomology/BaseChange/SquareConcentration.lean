/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.SquareConcentration

/-! # Original cartesian fibre and coefficient comparisons preserve K-cohomology -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyEquivOfSquare_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyEquivOfSquare_apply

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.FibreCohomologyConcentrated.of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.FibreCohomologyConcentrated.of_isPullback
