/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartAugmentation

open AlgebraicGeometry.Scheme.EtaleCohomology

/-! Native axiom guards for the original chart source and geometric pullback. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.chartComparisonSource_augmentation'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chartComparisonSource_augmentation

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.originalCohomologyChartEquiv_augmentation'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms originalCohomologyChartEquiv_augmentation

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.fibreProductCohomologyEquiv_globalTerminalClass'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fibreProductCohomologyEquiv_globalTerminalClass
