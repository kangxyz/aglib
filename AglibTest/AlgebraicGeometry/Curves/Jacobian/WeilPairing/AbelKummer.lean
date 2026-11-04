/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelKummer

/-! Axiom guard for the original Abel pullback of the original family class. -/

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.rootsCohomologyPullback_multiplicationFamilyKummerClass_jacobianCurveMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rootsCohomologyPullback_multiplicationFamilyKummerClass_jacobianCurveMorphism
