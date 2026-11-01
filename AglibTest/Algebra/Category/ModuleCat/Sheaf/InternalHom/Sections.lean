/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Sections

/-! # Original internal-Ext provider axiom guards -/

/-- info: 'SheafOfModules.InternalHom.sectionHomAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sectionHomAddEquiv

/-- info: 'SheafOfModules.InternalHom.sectionHomAddEquiv_map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sectionHomAddEquiv_map

/-- info: 'SheafOfModules.InternalHom.sectionHomAddEquiv_restrict' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sectionHomAddEquiv_restrict

/-- info: 'SheafOfModules.InternalHom.precompose_sections_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.precompose_sections_surjective

/-- info: 'SheafOfModules.InternalHom.precompose_epi_of_injective_over' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.precompose_epi_of_injective_over

/-- info: 'SheafOfModules.InternalHom.sectionHomNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sectionHomNatIso

/-- info: 'SheafOfModules.InternalHom.sectionHomNatIso_hom_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.sectionHomNatIso_hom_app_apply
