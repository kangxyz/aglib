/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Torsors.Restriction.Graph

/-! Axiom guard for the original comparison. -/

open AlgebraicGeometry.Scheme.Torsors.Restriction

/--
info: 'AlgebraicGeometry.Scheme.Torsors.Restriction.relativeCoverLift_act' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms relativeCoverLift_act
