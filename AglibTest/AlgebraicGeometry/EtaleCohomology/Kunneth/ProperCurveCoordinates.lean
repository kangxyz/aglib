/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ProperCurveCoordinates

/-! Axiom guard for proper-curve constant module Ext coordinates. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.properCurveConstantModuleExtAddEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms properCurveConstantModuleExtAddEquiv
