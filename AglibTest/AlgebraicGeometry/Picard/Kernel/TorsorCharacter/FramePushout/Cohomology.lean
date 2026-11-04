/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FramePushout.Cohomology

/-! Native axiom guards for the two original family cohomology equations. -/

open AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout.familyFrameClass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyFrameClass_eq

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout.familyCoframeClass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyCoframeClass_eq
