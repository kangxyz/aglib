/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ZMod

/-!
# Generic provider tests

These in-package checks retain independent universes and the approved axiom boundary
for every new public declaration in the corresponding provider.
-/

@[expose] public noncomputable section

/-- info: 'ModuleCat.uLiftZMod_forget₂_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.uLiftZMod_forget₂_full

/-- info: 'ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero

/-- info: 'ModuleCat.Sheaf.ConstantRing.uLiftZMod_toSheaf_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.uLiftZMod_toSheaf_full
