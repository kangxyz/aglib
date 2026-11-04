/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalFibreTrace

/-! Axiom guard for the original comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Curves

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_diagonalModuleKummerClass_pullback_sectionFibre'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms traceAddEquiv_diagonalModuleKummerClass_pullback_sectionFibre
