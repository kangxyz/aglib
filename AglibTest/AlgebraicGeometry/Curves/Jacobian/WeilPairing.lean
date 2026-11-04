/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing

/-! Axiom boundary for the canonical original Jacobian Weil pairing. -/

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianWeilPairingMorphism' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms jacobianWeilPairingMorphism
