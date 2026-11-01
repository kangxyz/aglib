/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelCurve

/-! # Original based curve-to-Jacobian map and its whole pointed formula -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.homEquiv_comp_jacobianCurveMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.homEquiv_comp_jacobianCurveMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianCurveMorphism_pointed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.jacobianCurveMorphism_pointed
