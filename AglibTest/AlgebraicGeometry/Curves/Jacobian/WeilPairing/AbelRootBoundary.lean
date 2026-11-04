/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelRootBoundary

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianAbelRootBoundaryEqNeg'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianAbelRootBoundaryEqNeg

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianTerminalFamilyKummerClass_eq_coverPush'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianTerminalFamilyKummerClass_eq_coverPush
