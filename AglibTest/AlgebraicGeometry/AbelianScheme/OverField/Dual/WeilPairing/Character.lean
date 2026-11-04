/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Character

/-! Axiom boundary for the original positive multiplication Cartier isomorphism. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.multiplicationKernelCartierIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms multiplicationKernelCartierIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.characterEquiv_comp_multiplicationKernelCartierHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms characterEquiv_comp_multiplicationKernelCartierHom
