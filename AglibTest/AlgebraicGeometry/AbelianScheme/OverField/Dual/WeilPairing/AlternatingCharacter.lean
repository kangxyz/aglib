/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.AlternatingCharacter

open AlgebraicGeometry.Scheme.RelativePicard

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.poincareKernelFrame_eq_polarizedKernelRatioFrame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poincareKernelFrame_eq_polarizedKernelRatioFrame

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.poincareKernelMultiplier_polarized_diagonal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poincareKernelMultiplier_polarized_diagonal
