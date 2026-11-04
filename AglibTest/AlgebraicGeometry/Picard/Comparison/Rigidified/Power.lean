/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified.Power

open AlgebraicGeometry.Scheme.RelativePicard

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.mapPowerIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RigidifiedPair.mapPowerIso

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.trivialPowerIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RigidifiedPair.trivialPowerIso
