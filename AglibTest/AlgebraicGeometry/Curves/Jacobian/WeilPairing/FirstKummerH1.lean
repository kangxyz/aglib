/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.FirstKummerH1

open AlgebraicGeometry.Scheme.OverField.Curve

/-! Native axiom guard for the original first-slot marked Kummer H¹ value. -/

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianFirstKummerH1'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianFirstKummerH1
