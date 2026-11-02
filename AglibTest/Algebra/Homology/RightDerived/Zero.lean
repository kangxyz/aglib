/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.RightDerived.Zero

/-! # Axiom guards for the original degree-zero derived-unit laws -/

/-- info: 'CategoryTheory.Functor.toRightDerivedZero_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.toRightDerivedZero_naturality

/-- info: 'CategoryTheory.Functor.toRightDerivedZero_postcomp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.toRightDerivedZero_postcomp
