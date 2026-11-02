/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.FieldComparison.GeometricPositive

/-! # Original Abel pullback and geometric positivity -/

@[expose] public section

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.geometricPositive_of_originalAbelPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms geometricPositive_of_originalAbelPullback
