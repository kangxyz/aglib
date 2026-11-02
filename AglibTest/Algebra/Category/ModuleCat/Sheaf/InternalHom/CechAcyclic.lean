/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.CechAcyclic

/-!
# Original internal-Hom provider axiom guards

The native provider retains its actual maps and conditions. These in-package
checks guard every new public declaration against nonstandard axioms.
-/

@[expose] public noncomputable section

/-- info: 'SheafOfModules.InternalHom.PresheafSource.tensorHomAddEquivRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.PresheafSource.tensorHomAddEquivRight

/-- info: 'PresheafOfModules.Cech.freeTensorHomAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.freeTensorHomAddEquiv

/-- info: 'PresheafOfModules.Cech.freeTensorHomAddEquiv_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.freeTensorHomAddEquiv_naturality

/-- info: 'PresheafOfModules.Cech.tensorHomComplexIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorHomComplexIso

/-- info: 'PresheafOfModules.Cech.internalHom_additiveHomComplex_exactAt_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.internalHom_additiveHomComplex_exactAt_succ

/-- info: 'SheafOfModules.InternalHom.familyCechAcyclic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.familyCechAcyclic

/-- info: 'SheafOfModules.InternalHom.cohomology_subsingleton_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.InternalHom.cohomology_subsingleton_of_injective
