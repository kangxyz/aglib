/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.Alternation

open AlgebraicGeometry.Scheme.OverField.Curve

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianWeilPairingMorphism_diagonal_of_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobianWeilPairingMorphism_diagonal_of_origin

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianWeilPairingMorphism_diagonal_of_genus_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobianWeilPairingMorphism_diagonal_of_genus_zero
