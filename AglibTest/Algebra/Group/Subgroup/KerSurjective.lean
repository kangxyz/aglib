/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Subgroup.KerSurjective

/-! Interface examples and approved-foundation guards for the shared provider. -/

@[expose] public section

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Kernel correction supplies the lift without a selected section. -/
example (r : A →+ B) (d : A →+ C) (hr : Function.Surjective r)
    (hd : Function.Surjective (d.comp r.ker.subtype)) (b : B) :
    ∃ a : A, d a = 0 ∧ r a = b := by
  obtain ⟨a, ha⟩ := AddMonoidHom.surjective_comp_ker_subtype r d hr hd b
  exact ⟨a, a.property, ha⟩

/-- info: 'AddMonoidHom.surjective_comp_ker_subtype' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddMonoidHom.surjective_comp_ker_subtype
