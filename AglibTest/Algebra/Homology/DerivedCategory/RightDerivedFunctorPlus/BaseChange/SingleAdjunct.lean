/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleAdjunct

/-! Axiom guard for the original single adjunct. -/

open CategoryTheory

/--
info: 'CategoryTheory.derivedUnitAdjunct_of_originalSingleExchange' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms derivedUnitAdjunct_of_originalSingleExchange
