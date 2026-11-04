/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.BaseChange

open AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.markedKernelBaseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms markedKernelBaseChange

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.markedKernelBaseChange_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms markedKernelBaseChange_boundary
