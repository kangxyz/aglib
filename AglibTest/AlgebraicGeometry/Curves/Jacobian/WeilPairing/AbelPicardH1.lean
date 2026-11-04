/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelPicardH1

open AlgebraicGeometry.Scheme.OverField.Curve

/-! Native axiom guard for the original Abel degree-one Picard map. -/

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianAbelPicardH1'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianAbelPicardH1
