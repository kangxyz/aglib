/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Binomial

/-!
# Uniqueness of binomial coefficients

`Int.eq_of_forall_sum_mul_choose_eq`: the coefficients `aᵢ` of a function
`r ↦ Σ_{i ≤ n} aᵢ C(r, i)`, `C = Ring.choose`, are determined by its values at the natural numbers.
At the least index `k` with `aₖ ≠ bₖ`, the difference of two such sums evaluates at `r = k` to
`aₖ - bₖ`. The Hilbert functions of projective subschemes use it to identify their binomial
coefficients.
-/

@[expose] public section

namespace Int

/-- **Binomial coefficients are unique**: if `Σ_{i ≤ n} aᵢ C(r, i) = Σ_{i ≤ n} bᵢ C(r, i)` for all
natural `r`, then `a = b`. At the least index `k` with `aₖ ≠ bₖ` the difference evaluates at
`r = k` to `aₖ - bₖ`, since `C(k, i) = 0` for `i > k` and `C(k, k) = 1`. -/
theorem eq_of_forall_sum_mul_choose_eq {n : ℕ} {a b : Fin (n + 1) → ℤ}
    (h : ∀ r : ℕ, ∑ i, a i * Ring.choose (r : ℤ) i = ∑ i, b i * Ring.choose (r : ℤ) i) :
    a = b := by
  classical
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ b j := Function.ne_iff.mp hne
  let S := Finset.univ.filter fun i => a i ≠ b i
  have hS : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let k := S.min' hS
  have hk : a k ≠ b k := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hlt (i : Fin (n + 1)) (hi : i < k) : a i = b i := by
    by_contra hne'
    exact absurd (S.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne'⟩)) (not_le.mpr hi)
  have key : ∑ i, (a i - b i) * Ring.choose ((k : ℕ) : ℤ) i = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, h k, sub_self]
  rw [Finset.sum_eq_single k] at key
  · rw [Ring.choose_natCast, Nat.choose_self, Nat.cast_one, mul_one, sub_eq_zero] at key
    exact hk key
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with hi | hi
    · rw [hlt i hi, sub_self, zero_mul]
    · rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (Fin.lt_def.mp hi), Nat.cast_zero,
        mul_zero]
  · intro hk'
    exact absurd (Finset.mem_univ k) hk'

end Int
