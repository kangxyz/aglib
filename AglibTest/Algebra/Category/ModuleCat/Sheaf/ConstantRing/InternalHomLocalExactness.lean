/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomLocalExactness

/-! # Original finite-chart internal-Hom proof axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleValuedOverFunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleValuedOverFunctor

/-- info: 'ModuleCat.Sheaf.ConstantRing.moduleValuedOverFunctor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.moduleValuedOverFunctor_additive

/-- info: 'ModuleCat.Sheaf.ConstantRing.exists_cover_boundary_of_presentation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.exists_cover_boundary_of_presentation

/-- info: 'ModuleCat.Sheaf.ConstantRing.locallyBoundary_injectiveResolution_of_constantTarget' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.locallyBoundary_injectiveResolution_of_constantTarget

/-- info: 'ModuleCat.Sheaf.ConstantRing.homFunctor_exactAt_of_finiteConstantCharts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.homFunctor_exactAt_of_finiteConstantCharts
