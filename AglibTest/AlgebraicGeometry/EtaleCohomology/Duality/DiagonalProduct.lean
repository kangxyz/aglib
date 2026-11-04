/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalProduct

/-! Axiom guard for the original comparison. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.diagonalModuleKummerClass_projection_comp'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diagonalModuleKummerClass_projection_comp

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.diagonalModuleKummerClass_pullback_sectionFibre'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diagonalModuleKummerClass_pullback_sectionFibre

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.abelModuleKummerClass_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelModuleKummerClass_eq
