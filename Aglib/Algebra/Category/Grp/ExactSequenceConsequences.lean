/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Exact.Basic

/-! # Consequences of actual additive exact maps

These consequences keep the displayed homomorphisms and independent group
universes. They introduce no cohomology or replacement exact-sequence object.
-/

@[expose] public section

namespace AddCommGroupExact

universe uA uB uC uD

/-- Two exact pairs and an injective last map make the first map surjective. -/
theorem surjective_of_exact_of_injective {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    (d : A →+ B) (i : B →+ C) (p : C →+ D)
    (hdi : Function.Exact d i) (hip : Function.Exact i p)
    (hp : Function.Injective p) : Function.Surjective d := by
  intro b
  apply (hdi b).mp
  apply hp
  exact (hip.apply_apply_eq_zero b).trans (map_zero p).symm

/-- Two surjective maps in an exact pair have zero final group. -/
theorem subsingleton_of_exact_of_surjective {A : Type uA} {B : Type uB} {C : Type uC}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (p : A →+ B) (d : B →+ C) (hpd : Function.Exact p d)
    (hp : Function.Surjective p) (hd : Function.Surjective d) : Subsingleton C := by
  apply subsingleton_of_forall_eq (0 : C)
  intro c
  obtain ⟨b, rfl⟩ := hd c
  obtain ⟨a, rfl⟩ := hp b
  exact hpd.apply_apply_eq_zero a

/-- Exactness with zero outside groups makes the actual middle map bijective. -/
theorem bijective_of_exact_subsingleton {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Subsingleton A] [Subsingleton D] (i : A →+ B) (p : B →+ C) (d : C →+ D)
    (hi : Function.Exact i p) (hd : Function.Exact p d) : Function.Bijective p := by
  constructor
  · intro x y hxy
    have hz : p (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ := (hi (x - y)).mp hz
    apply sub_eq_zero.mp
    exact ha.symm.trans (by rw [Subsingleton.elim a 0, map_zero])
  · intro y
    exact (hd y).mp (Subsingleton.elim _ _)

end AddCommGroupExact
