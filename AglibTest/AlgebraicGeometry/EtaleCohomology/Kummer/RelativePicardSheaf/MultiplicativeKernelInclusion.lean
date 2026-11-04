/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.MultiplicativeKernelInclusion

/-! Axiom guard for the original multiplicative kernel comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Picard

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.gmHigherDirectImageNormalizedPicardIso_inclusion'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gmHigherDirectImageNormalizedPicardIso_inclusion
