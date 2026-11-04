/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.SectionTrace

/-! Approved-axiom guards for the retained original declarations. -/

/--
info: 'CategoryTheory.CorrectedExchangeLoop.of_original_values' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.CorrectedExchangeLoop.of_original_values
