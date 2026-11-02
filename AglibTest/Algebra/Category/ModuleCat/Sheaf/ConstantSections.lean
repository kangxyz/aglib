/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantSections

/-! # Original section-supplier axiom guards -/

/-- info: 'ModuleCat.Sheaf.constantSliceHomAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantSliceHomAddEquiv

/-- info: 'ModuleCat.Sheaf.constantSliceHomAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantSliceHomAddEquiv_apply

/-- info: 'ModuleCat.Sheaf.constantSliceHomAddEquiv_symm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantSliceHomAddEquiv_symm

/-- info: 'ModuleCat.Sheaf.constantSliceHomNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantSliceHomNatIso

/-- info: 'ModuleCat.Sheaf.constantSliceHomNatIso_hom_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantSliceHomNatIso_hom_app_apply
