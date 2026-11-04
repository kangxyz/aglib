/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare.Power

open AlgebraicGeometry.Scheme.RelativePicard

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.poincarePowerIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poincarePowerIso

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.poincarePullbackPowerIso_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poincarePullbackPowerIso_naturality

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.poincarePullbackPowerIso_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poincarePullbackPowerIso_unit
