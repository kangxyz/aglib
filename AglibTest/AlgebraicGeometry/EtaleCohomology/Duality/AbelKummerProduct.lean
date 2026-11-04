/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.AbelKummerProduct

/-! Axiom guard for the original comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.firstPullback_comp_abelModuleKummerClass'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms firstPullback_comp_abelModuleKummerClass
