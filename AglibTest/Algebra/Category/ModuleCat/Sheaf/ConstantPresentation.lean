/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantPresentation

/-! # Original constant-presentation construction axiom guards -/

/-- info: 'ModuleCat.Sheaf.constantPresentationIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantPresentationIso

/-- info: 'ModuleCat.Sheaf.constantPresentationIso_hom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantPresentationIso_hom

/-- info: 'ModuleCat.Sheaf.constantPresentationIso_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantPresentationIso_unit

/-- info: 'ModuleCat.Sheaf.constantPresentationIso_eq_of_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantPresentationIso_eq_of_unit

/-- info: 'ModuleCat.Sheaf.constantPresentationIso_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.constantPresentationIso_naturality

/-- info: 'ModuleCat.Sheaf.overPresentationRestrict' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPresentationRestrict

/-- info: 'ModuleCat.Sheaf.overPresentationRestrict_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPresentationRestrict_id

/-- info: 'ModuleCat.Sheaf.overPresentationRestrict_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPresentationRestrict_comp

/-- info: 'ModuleCat.Sheaf.overPresentationRestrict_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPresentationRestrict_terminal

/-- info: 'ModuleCat.Sheaf.overPresentationRestrict_isLocallySurjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPresentationRestrict_isLocallySurjective

/-- info: 'ModuleCat.Sheaf.overPresentationRestrict_isLocallyInjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPresentationRestrict_isLocallyInjective
