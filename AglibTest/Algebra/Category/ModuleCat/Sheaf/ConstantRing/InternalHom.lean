/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHom

/-! # Original constant-ring slice Hom comparison axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.overHomValuedAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overHomValuedAddEquiv

/-- info: 'ModuleCat.Sheaf.ConstantRing.overHomValuedAddEquiv_apply_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overHomValuedAddEquiv_apply_app

/-- info: 'ModuleCat.Sheaf.ConstantRing.overHomValuedNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.overHomValuedNatIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv

/-- info: 'ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv_apply_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv_apply_app

/-- info: 'ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv_precompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv_precompose

/-- info: 'ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv_postcompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sectionValuedHomAddEquiv_postcompose
