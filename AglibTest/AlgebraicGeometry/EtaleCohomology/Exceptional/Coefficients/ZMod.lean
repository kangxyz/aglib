/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ZMod

/-!
# Generic provider tests

These in-package checks retain independent universes and the approved axiom boundary
for every new public declaration in the corresponding provider.
-/

@[expose] public noncomputable section

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCat_uLiftZMod_forget₂_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCat_uLiftZMod_forget₂_full

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_toSheaf_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_toSheaf_full
