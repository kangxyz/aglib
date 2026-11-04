/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdgeTrace

/-! Axiom guard for the original comparison. -/

/--
info: 'DerivedCategory.Plus.mixedEdge_precomp_topSingle_trace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DerivedCategory.Plus.mixedEdge_precomp_topSingle_trace

/--
info: 'DerivedCategory.Plus.mixedEdge_precomp_topSingle_shiftedTrace'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DerivedCategory.Plus.mixedEdge_precomp_topSingle_shiftedTrace

/--
info: 'DerivedCategory.Plus.singleShiftTrace_homology_value'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DerivedCategory.Plus.singleShiftTrace_homology_value
