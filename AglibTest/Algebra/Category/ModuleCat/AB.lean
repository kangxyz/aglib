/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.AB

/-! # Independent scalar, value and coproduct-index size checks -/

open CategoryTheory

universe r m w

example (Λ : Type r) [Ring Λ] : AB4OfSize.{w} (ModuleCat.{max w m} Λ) := inferInstance

/-- info: 'ModuleCat.ab4Independent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.ab4Independent

/-- info: 'ModuleCat.ab4OfSizeIndependent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.ab4OfSizeIndependent
