/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Integer facts about binomial coefficients

Facts about Mathlib's `Ring.choose` on `ℤ`, written `C(x, i)`: Pascal's rule in the difference
form `C(x, i + 1) - C(x - 1, i + 1) = C(x - 1, i)` (`Ring.choose_succ_sub_choose_pred`), the
bounds `0 ≤ C(y, i) ≤ yⁱ` for `y ≥ 0` (`Ring.choose_nonneg_le_pow`) and
`-a C(y, i) ≤ a² yⁱ` (`Ring.neg_mul_choose_le`), and the integration of a binomial forward
difference: if `f (m + 1) - f m = Σ_{i < N} bᵢ C(m, i)` for all `m : ℤ`, then
`f m = Σ_{i < N + 1} aᵢ C(m, i)` with `a₀ = f 0` and `a_{i + 1} = bᵢ`
(`Int.eq_sum_choose_of_fwdDiff`). The Hilbert functions of coherent modules on projective space
and Mumford's bound consume them.
-/

@[expose] public section

namespace Ring

/-- Pascal's rule in the form `C(x, i + 1) - C(x - 1, i + 1) = C(x - 1, i)`. -/
theorem choose_succ_sub_choose_pred (x : ℤ) (i : ℕ) :
    Ring.choose x (i + 1) - Ring.choose (x - 1) (i + 1) = Ring.choose (x - 1) i := by
  have h := Ring.choose_succ_succ (x - 1) i
  rw [sub_add_cancel] at h
  rw [h]
  ring

/-- `0 ≤ C(y, i) ≤ yⁱ` for `y ≥ 0`. -/
theorem choose_nonneg_le_pow {y : ℤ} (hy : 0 ≤ y) (i : ℕ) :
    0 ≤ Ring.choose y i ∧ Ring.choose y i ≤ y ^ i := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  rw [Ring.choose_natCast]
  exact ⟨by positivity, by exact_mod_cast Nat.choose_le_pow m i⟩

/-- `-a C(y, i) ≤ a² yⁱ` for `y ≥ 0`. -/
theorem neg_mul_choose_le (a : ℤ) {y : ℤ} (hy : 0 ≤ y) (i : ℕ) :
    -(a * Ring.choose y i) ≤ a ^ 2 * y ^ i := by
  obtain ⟨h0, h1⟩ := choose_nonneg_le_pow hy i
  have hp : 0 ≤ y ^ i := pow_nonneg hy i
  rcases le_or_gt 0 a with ha | ha
  · nlinarith [mul_nonneg ha h0, mul_nonneg (sq_nonneg a) hp]
  · have h2 : -a * Ring.choose y i ≤ -a * y ^ i :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : -a ≤ a ^ 2 := by nlinarith
    have h4 : -a * y ^ i ≤ a ^ 2 * y ^ i := mul_le_mul_of_nonneg_right h3 hp
    linarith

end Ring

namespace Int

/-- If the forward difference of `f : ℤ → ℤ` is `Σ_{i < N} bᵢ C(m, i)`, then
`f m = Σ_{i < N + 1} aᵢ C(m, i)` with `a₀ = f 0` and `a_{i + 1} = bᵢ`. -/
theorem eq_sum_choose_of_fwdDiff {f : ℤ → ℤ} {N : ℕ} (b : Fin N → ℤ)
    (h : ∀ m : ℤ, f (m + 1) - f m = ∑ i : Fin N, b i * Ring.choose m i) (m : ℤ) :
    f m = ∑ i : Fin (N + 1), (Fin.cons (f 0) b : Fin (N + 1) → ℤ) i * Ring.choose m i := by
  let g : ℤ → ℤ := fun m =>
    ∑ i : Fin (N + 1), (Fin.cons (f 0) b : Fin (N + 1) → ℤ) i * Ring.choose m i
  have hg (m : ℤ) : g (m + 1) - g m = ∑ i : Fin N, b i * Ring.choose m i := by
    simp only [g, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ,
      Ring.choose_zero_right, Ring.choose_succ_succ, mul_add, Finset.sum_add_distrib]
    ring
  have h0 : f 0 = g 0 := by
    simp [g, Fin.sum_univ_succ, Ring.choose_zero_succ]
  change f m = g m
  induction m using Int.induction_on with
  | zero => exact h0
  | succ i ih =>
    have h₁ := h i
    have h₂ := hg i
    linarith
  | pred i ih =>
    have h₁ := h (-i - 1)
    have h₂ := hg (-i - 1)
    simp only [sub_add_cancel] at h₁ h₂
    linarith

end Int
