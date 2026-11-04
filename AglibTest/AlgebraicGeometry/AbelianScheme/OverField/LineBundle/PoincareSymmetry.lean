/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.PoincareSymmetry

open AlgebraicGeometry.Scheme.RelativePicard

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.polarizedSwap_diagonal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarizedSwap_diagonal

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.polarizedFirstPowerIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarizedFirstPowerIso

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.polarizedSecondPowerIso_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarizedSecondPowerIso_unit

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.polarizedPower_diagonal_trivializations'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarizedPower_diagonal_trivializations
