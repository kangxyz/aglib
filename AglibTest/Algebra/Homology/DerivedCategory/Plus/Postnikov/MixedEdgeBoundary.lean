/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdgeBoundary

/-! Axiom guard for the original comparison. -/

/--
info: 'DerivedCategory.Plus.mixedEdgeTrace_boundary_of_comparison'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DerivedCategory.Plus.mixedEdgeTrace_boundary_of_comparison
