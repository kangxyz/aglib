/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.SurjectiveLift

/-! # Original geometric field tests lift through LFT surjective maps -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.Hom.exists_lift_spec_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.exists_lift_spec_of_isAlgClosed
