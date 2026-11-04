/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.SingleAdjunct

/-! Axiom guard for the original single adjunct. -/

open CategoryTheory.Adjunction

/--
info: 'CategoryTheory.Adjunction.rightDerivedFunctorPlus_homEquiv_single' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightDerivedFunctorPlus_homEquiv_single
