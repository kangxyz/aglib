/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ConstantMap

/-! Axiom guards for the original constant-coefficient external product. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.constantModuleExtExternalProduct'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constantModuleExtExternalProduct

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.constantModuleExtKunnethMap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constantModuleExtKunnethMap
