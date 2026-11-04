/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Fibre

/-! Axiom guard for the original top-homology restriction fibre. -/

open DerivedCategory.Plus

/--
info: 'DerivedCategory.Plus.postnikovFibreHomology' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms postnikovFibreHomology

/--
info: 'DerivedCategory.Plus.exists_postnikovRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_postnikovRestriction

/--
info: 'DerivedCategory.Plus.exists_postnikovMultiplicationFibre_comparison' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_postnikovMultiplicationFibre_comparison
