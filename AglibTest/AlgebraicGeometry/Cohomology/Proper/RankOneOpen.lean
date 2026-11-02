/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.RankOneOpen

/-! # Original rank-one open and actual geometric concentration -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isOpen_setOf_modulePointFiber_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isOpen_setOf_modulePointFiber_rankOne

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyConcentrated_rankOneOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyConcentrated_rankOneOpen
