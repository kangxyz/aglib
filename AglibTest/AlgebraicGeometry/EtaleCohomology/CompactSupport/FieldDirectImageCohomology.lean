/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldDirectImageCohomology

/-! Axiom guards for the original field direct-image comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.moduleFieldDerivedUnitHomologyAddEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleFieldDerivedUnitHomologyAddEquiv

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.moduleFieldDirectImageHomologyAddEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleFieldDirectImageHomologyAddEquiv
