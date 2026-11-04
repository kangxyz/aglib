/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Section

/-! Approved-axiom guards for the retained original declarations. -/

/--
info: 'CategoryTheory.Functor.rightDerivedSingle_sectionValue_of_original_family' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedSingle_sectionValue_of_original_family
