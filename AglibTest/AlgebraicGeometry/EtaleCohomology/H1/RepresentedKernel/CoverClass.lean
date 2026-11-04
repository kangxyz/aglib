/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverClass

/-! Axiom guard for the original cover class. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.relativeCoverExtClass_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms relativeCoverExtClass_eq
