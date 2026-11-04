/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdge

/-! Axiom guards for the original top projection and mixed edge. -/

open DerivedCategory.Plus

/--
info: 'DerivedCategory.Plus.upperHomologyProjection_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms upperHomologyProjection_naturality

/--
info: 'DerivedCategory.Plus.mixedEdge_negative_transgression_homology' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mixedEdge_negative_transgression_homology

/--
info: 'DerivedCategory.Plus.upperHomologyProjection_homology' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms upperHomologyProjection_homology

/--
info: 'DerivedCategory.Plus.mixedEdge_precomp_topSingle_inverseAdjunct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mixedEdge_precomp_topSingle_inverseAdjunct
