/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MultiplicationFibre

open DerivedCategory.Plus

/-! Axiom guards for the original H1 multiplication-fibre kernel and inclusion. -/

/--
info: 'DerivedCategory.Plus.homologyOneKernelIsoOfEpiZero'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms homologyOneKernelIsoOfEpiZero

/--
info: 'DerivedCategory.Plus.homologyOneMultiplicationKernelIso_hom_ι'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms homologyOneMultiplicationKernelIso_hom_ι
