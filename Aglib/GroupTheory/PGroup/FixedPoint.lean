/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.PGroup

/-! # Nonzero fixed points in finite prime-torsion groups

Only the underlying finite action and its fixed zero are required. The native
order of any nonzero coefficient is p, so native finite-group divisibility
supplies the required cardinal divisibility without choosing a module structure.
-/

@[expose] public noncomputable section

namespace IsPGroup

universe g v

/-- A p-group action fixing zero on a nontrivial finite p-torsion abelian group
has a nonzero fixed point, even without an additive-action hypothesis. -/
theorem exists_ne_zero_fixedPoint_of_annihilated
    {p : ℕ} [Fact p.Prime] {G : Type g} [Group G]
    {V : Type v} [AddCommGroup V] [Finite V] [Nontrivial V] [MulAction G V]
    (hG : IsPGroup p G) (hzero : ∀ g : G, g • (0 : V) = 0)
    (hV : ∀ x : V, p • x = 0) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : G, g • x = x := by
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  let x : Multiplicative V := Multiplicative.ofAdd a
  have hx : x ≠ 1 := ha
  have hxp : x ^ p = 1 := hV a
  have hord : orderOf x = p := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf x)
      (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · exact False.elim (hx (orderOf_eq_one_iff.mp h))
    · exact h
  have hdiv : p ∣ Nat.card V := by
    rw [← hord]
    exact orderOf_dvd_natCard x
  obtain ⟨x, hx, h0x⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdiv hzero
  exact ⟨x, Ne.symm h0x, hx⟩

end IsPGroup
