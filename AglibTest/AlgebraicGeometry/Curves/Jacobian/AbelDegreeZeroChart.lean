/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelDegreeZeroChart

/-! Axiom guards for the original Abel chart. -/

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.abelTerminalFamilyClass_pullback'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.abelTerminalFamilyClass_pullback

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianAbelTerminalChartValue'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.jacobianAbelTerminalChartValue

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianAbelTerminalGraphNormalizedValue'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.jacobianAbelTerminalGraphNormalizedValue
