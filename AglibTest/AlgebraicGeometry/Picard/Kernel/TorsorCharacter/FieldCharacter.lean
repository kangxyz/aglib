/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FieldCharacter

/-! Axiom boundary for comparing original characters from their multipliers. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.kernelTrivializationCharacter_fieldBaseChange_of_multiplier'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kernelTrivializationCharacter_fieldBaseChange_of_multiplier

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.kernelTrivializationCharacter_fieldBaseChange_of_multiplier_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kernelTrivializationCharacter_fieldBaseChange_of_multiplier_eq
