/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.MultiplicativeComparison

/-! Axiom guards for the original multiplicative direct-image comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Picard

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.gmHigherDirectImageNormalizedPicardIso_unit'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gmHigherDirectImageNormalizedPicardIso_unit

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.gmHigherDirectImageNormalizedPicardIso_power'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gmHigherDirectImageNormalizedPicardIso_power
