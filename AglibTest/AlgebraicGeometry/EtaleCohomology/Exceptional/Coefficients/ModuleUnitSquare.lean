/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitSquare

/-! Axiom guard for the original comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitInverseImageIso_square_reflected'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnitInverseImageIso_square_reflected
