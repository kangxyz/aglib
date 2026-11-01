/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FiniteConstantCharts

/-! # Original finite-type chart covering sieve axiom guards -/

/-- info: 'ModuleCat.Sheaf.finiteTypeConstantChartSieve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.finiteTypeConstantChartSieve

/-- info: 'ModuleCat.Sheaf.finiteTypeConstantChartSieve_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.finiteTypeConstantChartSieve_pullback

/-- info: 'ModuleCat.Sheaf.HasFiniteTypeConstantCharts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.HasFiniteTypeConstantCharts

/-- info: 'ModuleCat.Sheaf.hasFiniteTypeConstantCharts_of_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.hasFiniteTypeConstantCharts_of_terminal
