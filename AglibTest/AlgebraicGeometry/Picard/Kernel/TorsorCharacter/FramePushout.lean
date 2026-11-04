/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FramePushout

/-! Native axiom guards for the two original cover comparison maps. -/

open AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout.familyFramePushoutIso_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyFramePushoutIso_map

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout.familyCoframePushoutIso_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyCoframePushoutIso_map

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout.familyCoverExtClassEq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyCoverExtClassEq
