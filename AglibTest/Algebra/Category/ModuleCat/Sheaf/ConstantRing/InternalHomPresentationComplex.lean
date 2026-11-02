/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomPresentationComplex

/-! # Original whole coefficient/presheaf/complex comparison axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.internalHomOverPresheafFunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.internalHomOverPresheafFunctor

/-- info: 'ModuleCat.Sheaf.ConstantRing.valuedHomOverPresheafFunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.valuedHomOverPresheafFunctor

/-- info: 'ModuleCat.Sheaf.ConstantRing.internalHomOverPresheafFunctor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.internalHomOverPresheafFunctor_additive

/-- info: 'ModuleCat.Sheaf.ConstantRing.valuedHomOverPresheafFunctor_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.valuedHomOverPresheafFunctor_additive

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationPresheafNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationPresheafNatIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationPresheafNatIso_hom_app_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationPresheafNatIso_hom_app_app_apply

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationComplexIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationComplexIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationComplexIso_hom_f_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationComplexIso_hom_f_app_apply
