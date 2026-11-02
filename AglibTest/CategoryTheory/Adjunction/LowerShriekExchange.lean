/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.LowerShriekExchange

/-! Whole original exchange laws over independent categories. -/

/-- info: 'CategoryTheory.Adjunction.LowerShriekExchange.comparison_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.LowerShriekExchange.comparison_unit

/-- info: 'CategoryTheory.Adjunction.LowerShriekExchange.coefficient_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.LowerShriekExchange.coefficient_unit
