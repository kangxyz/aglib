/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback

/-! Axiom guards for the original comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.constantModuleExtPullback_homPlus'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constantModuleExtPullback_homPlus

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.constantModuleExtPullbackShiftedMateValue'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constantModuleExtPullbackShiftedMateValue
