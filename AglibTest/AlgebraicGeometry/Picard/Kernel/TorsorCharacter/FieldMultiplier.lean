/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FieldMultiplier

/-! Axiom boundary for scalar extension of the original kernel multiplier. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.kernelMultiplier_fieldBaseChange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms kernelMultiplier_fieldBaseChange
