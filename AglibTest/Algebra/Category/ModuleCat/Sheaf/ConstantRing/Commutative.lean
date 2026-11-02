/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Commutative

/-!
# Original internal-Hom provider axiom guards

The native provider retains its actual maps and conditions. These in-package
checks guard every new public declaration against nonstandard axioms.
-/

@[expose] public noncomputable section

/-- info: 'ModuleCat.Sheaf.ConstantRing.section_mul_comm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.section_mul_comm

/-- info: 'ModuleCat.Sheaf.ConstantRing.commRingSection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.commRingSection

/-- info: 'ModuleCat.Sheaf.ConstantRing.commutativePresheaf' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.commutativePresheaf

/-- info: 'ModuleCat.Sheaf.ConstantRing.commutativePresheaf_forget' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.commutativePresheaf_forget

/-- info: 'ModuleCat.Sheaf.ConstantRing.commutativeSheaf' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.commutativeSheaf

/-- info: 'ModuleCat.Sheaf.ConstantRing.commutativeSheaf_forget' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.commutativeSheaf_forget
