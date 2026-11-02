/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomAcyclic

/-! # Original finite-chart internal-Hom proof axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.isZero_rightDerived_of_finiteConstantCharts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.isZero_rightDerived_of_finiteConstantCharts

/-- info: 'ModuleCat.Sheaf.ConstantRing.isZero_rightDerived_moduleUnit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.isZero_rightDerived_moduleUnit
