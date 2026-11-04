/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.DiagonalFibre

/-! Axiom guard for the original comparison. -/

open AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor.diagonalIdealClass_pullback_sectionFibre' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diagonalIdealClass_pullback_sectionFibre

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor.abelClass_identity_eq_diagonal_sub_origin'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelClass_identity_eq_diagonal_sub_origin
