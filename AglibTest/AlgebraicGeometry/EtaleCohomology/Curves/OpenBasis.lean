/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.OpenBasis

/-! Axiom guards for bases of the original roots and constant H1. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Curves

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsOneOpenBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rootsOneOpenBasis

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantOneOpenBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constantOneOpenBasis
