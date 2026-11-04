/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomologyHomPlus

/-! Axiom guard for the original comparison. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsUnitExtCohomologyAddEquiv_homPlus'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsUnitExtCohomologyAddEquiv_homPlus

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtCohomologyAddEquiv_homPlus'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitExtCohomologyAddEquiv_homPlus
