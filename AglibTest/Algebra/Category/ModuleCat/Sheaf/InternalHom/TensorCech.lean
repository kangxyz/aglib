/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.TensorCech

/-!
# Original internal-Hom provider axiom guards

The native provider retains its actual maps and conditions. These in-package
checks guard every new public declaration against nonstandard axioms.
-/

@[expose] public noncomputable section

/-- info: 'PresheafOfModules.Cech.tensorRight_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorRight_additive

/-- info: 'PresheafOfModules.Cech.tensorFreeComplex' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorFreeComplex

/-- info: 'PresheafOfModules.Cech.tensorImageAugmentation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorImageAugmentation

/-- info: 'PresheafOfModules.Cech.tensorImageAugmentation_quasiIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorImageAugmentation_quasiIso

/-- info: 'PresheafOfModules.Cech.tensorFreeComplex_exactAt_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorFreeComplex_exactAt_succ

/-- info: 'PresheafOfModules.Cech.tensorHomComplex' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorHomComplex

/-- info: 'PresheafOfModules.Cech.tensorHomComplex_exactAt_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.Cech.tensorHomComplex_exactAt_succ
