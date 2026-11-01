/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicCartier

/-! # Original intrinsic theta Cartier divisor in the existing degree stratum -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isEffectiveCartier_intrinsicTheta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isEffectiveCartier_intrinsicTheta
