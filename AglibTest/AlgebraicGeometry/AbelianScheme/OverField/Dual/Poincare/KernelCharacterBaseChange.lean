/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare.KernelCharacterBaseChange

/-! Axiom boundary for scalar extension of the original Poincare kernel character. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.poincareKernelCharacter_fieldBaseChange_of_map_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms poincareKernelCharacter_fieldBaseChange_of_map_eq
