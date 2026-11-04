/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.RootFieldBaseChange

/-! Axiom boundary for scalar extension of the original root-valued Weil pairing. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.weilPairingMorphism_fieldBaseChange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms weilPairingMorphism_fieldBaseChange
