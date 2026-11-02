/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomPresentation

/-! # Original presentation-based internal-Hom comparison axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationHomNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationHomNatIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_apply

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_apply_apply

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_postcompose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_postcompose

/-- info: 'ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_restrict' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.presentationSectionAddEquiv_restrict
