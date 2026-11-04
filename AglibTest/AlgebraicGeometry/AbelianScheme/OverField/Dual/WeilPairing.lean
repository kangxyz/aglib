/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Transpose

/-! Axiom boundary for the same original roots-valued Weil pairing. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.weilPairingMorphism_comp_inclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms weilPairingMorphism_comp_inclusion

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.weilPairingMorphism_comp_inclusion_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms weilPairingMorphism_comp_inclusion_transpose
