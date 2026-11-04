/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified.Symmetry

open AlgebraicGeometry.Scheme.RelativePicard

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.mapToTrivial_originFrame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RigidifiedPair.mapToTrivial_originFrame

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.lineBundleIso_eq_of_pullbackMap_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lineBundleIso_eq_of_pullbackMap_eq
