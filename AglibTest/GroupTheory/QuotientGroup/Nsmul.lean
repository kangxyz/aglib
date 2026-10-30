/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.QuotientGroup.Nsmul

/-! Interface examples and approved-foundation guards for the shared provider. -/

@[expose] public section

open QuotientAddGroup

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The degree equivalence retains the actual integer-valued homomorphism. -/
example (d : A →+ ℤ) (hd : Function.Surjective d) (n : ℕ)
    (hker : Function.Surjective (nsmulAddMonoidHom (α := d.ker) n)) (a : A) :
    nsmulEquivZMod d hd n hker (mk a) = (d a : ZMod n) :=
  nsmulEquivZMod_mk d hd n hker a

/-- Level one remains admitted, including without a nontriviality hypothesis. -/
example (f : A →+ B) (hf : Function.Surjective f) :
    Nonempty (A ⧸ (nsmulAddMonoidHom (α := A) 1).range ≃+
      B ⧸ (nsmulAddMonoidHom (α := B) 1).range) := by
  exact ⟨nsmulEquivOfSurjectiveOfKer f hf 1 (fun a => ⟨a, one_nsmul a⟩)⟩

/-- Commuting maps retain their whole square after passing to quotients. -/
example (f : A →+ B) (n : ℕ) :
    (nsmulMap (AddMonoidHom.id B) n).comp (nsmulMap f n) =
      (nsmulMap f n).comp (nsmulMap (AddMonoidHom.id A) n) :=
  nsmulMap_naturality f f (AddMonoidHom.id A) (AddMonoidHom.id B) rfl n

/-- info: 'QuotientAddGroup.nsmulMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulMap

/-- info: 'QuotientAddGroup.nsmulMap_mk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulMap_mk

/-- info: 'QuotientAddGroup.nsmulMap_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulMap_id

/-- info: 'QuotientAddGroup.nsmulMap_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulMap_comp

/-- info: 'QuotientAddGroup.nsmulMap_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulMap_naturality

/-- info: 'QuotientAddGroup.nsmulMap_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulMap_surjective

/-- info: 'QuotientAddGroup.nsmulMap_injective_of_surjective_of_ker' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulMap_injective_of_surjective_of_ker

/-- info: 'QuotientAddGroup.nsmulEquivOfSurjectiveOfKer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulEquivOfSurjectiveOfKer

/-- info: 'QuotientAddGroup.nsmulEquivOfSurjectiveOfKer_toAddMonoidHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulEquivOfSurjectiveOfKer_toAddMonoidHom

/-- info: 'QuotientAddGroup.int_nsmul_range' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.int_nsmul_range

/-- info: 'QuotientAddGroup.nsmulEquivZMod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulEquivZMod

/-- info: 'QuotientAddGroup.nsmulEquivZMod_comp_mk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulEquivZMod_comp_mk

/-- info: 'QuotientAddGroup.nsmulEquivZMod_mk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.nsmulEquivZMod_mk

/-- info: 'QuotientAddGroup.intCast_comp_ker_eq_nsmul_range' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientAddGroup.intCast_comp_ker_eq_nsmul_range

/-- info: 'AddEquiv.ker_comp_eq_range_nsmul_of_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddEquiv.ker_comp_eq_range_nsmul_of_exact
