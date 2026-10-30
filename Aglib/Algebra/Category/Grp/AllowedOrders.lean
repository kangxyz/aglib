/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.GroupTheory.OrderOfElement

/-! # Positive unit annihilators and the actual additive order

The ring and additive group have independent universes. This is the unit case,
not an assertion for arbitrary allowed submonoids without divisor closure.
-/

@[expose] public noncomputable section

namespace AddGroup

universe u v

/-- A positive unit annihilator is equivalent to a finite additive order
which is a unit in the same original ring. -/
theorem exists_pos_unit_annihilator_iff (R : Type u) [CommRing R]
    {A : Type v} [AddGroup A] (z : A) :
    (∃ n : ℕ, 0 < n ∧ IsUnit (n : R) ∧ n • z = 0) ↔
      IsOfFinAddOrder z ∧ IsUnit (addOrderOf z : R) := by
  constructor
  · rintro ⟨n, hn, hm, hs⟩
    refine ⟨isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hs⟩,
      isUnit_of_dvd_unit ?_ hm⟩
    obtain ⟨m, he⟩ := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hs
    refine ⟨(m : R), ?_⟩
    simpa only [Nat.cast_mul] using congrArg (fun k : ℕ => (k : R)) he
  · rintro ⟨hf, hu⟩
    exact ⟨addOrderOf z, hf.addOrderOf_pos, hu, addOrderOf_nsmul_eq_zero z⟩

end AddGroup
