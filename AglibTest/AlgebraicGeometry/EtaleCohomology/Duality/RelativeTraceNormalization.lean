/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RelativeTraceNormalization

/-! Axiom guards for the original normalized ordinary and shifted relative trace. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.properCurveFieldOrdinaryTrace_normalized'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms properCurveFieldOrdinaryTrace_normalized

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.properCurveDiagonalOrdinaryTraceExistsUniqueNormalized'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms properCurveDiagonalOrdinaryTraceExistsUniqueNormalized

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.properCurveDiagonalTraceExistsNormalized'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms properCurveDiagonalTraceExistsNormalized
