/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.PullbackComposition

/-! Axiom guards for the original comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.constantModuleExtPullback_comp'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constantModuleExtPullback_comp

open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.moduleRootsUnitExtPullback_comp_constant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleRootsUnitExtPullback_comp_constant
