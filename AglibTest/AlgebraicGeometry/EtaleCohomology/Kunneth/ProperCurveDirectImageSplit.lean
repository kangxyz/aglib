/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ProperCurveDirectImageSplit

/-! Axiom guard for the actual proper-curve derived splitting. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.properCurveConstantDirectImageSplitIso'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms properCurveConstantDirectImageSplitIso
