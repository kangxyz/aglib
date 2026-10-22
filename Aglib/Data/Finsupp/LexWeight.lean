/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Positive weights isolating one lexicographic exponent

For a fixed exponent in a positive finite number of variables, positive
integer weights with last weight one make its weight strictly smaller than
every lexicographically larger exponent. This is not an order embedding of
the entire exponent space. No ring, field, or characteristic is involved.
-/

@[expose] public section

namespace Finsupp

private theorem exists_pos_lexWeight_aux (n : ℕ) (a : Fin (n + 1) → ℕ) :
    ∃ w : Fin (n + 1) → ℕ,
      (∀ i, 0 < w i) ∧ w (Fin.last n) = 1 ∧
      ∀ b : Fin (n + 1) → ℕ,
        (∃ j, (∀ i, i < j → a i = b i) ∧ a j < b j) →
          (∑ i, a i * w i) < ∑ i, b i * w i := by
  induction n with
  | zero =>
      refine ⟨fun _ ↦ 1, fun _ ↦ Nat.zero_lt_one, rfl, ?_⟩
      intro b h
      obtain ⟨j, _, hj⟩ := h
      have hj0 : j = 0 := by
        apply Fin.ext
        have hjlt := j.isLt
        change j.val = 0
        omega
      subst j
      simpa using hj
  | succ n ih =>
      obtain ⟨w, hw, hlast, hlex⟩ := ih (fun i ↦ a i.succ)
      let t : ℕ := ∑ i, a i.succ * w i
      let W : Fin (n + 2) → ℕ := Fin.cons (t + 1) w
      refine ⟨W, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change 0 < t + 1
          omega
        · exact hw j
      · change w (Fin.last n) = 1
        exact hlast
      · intro b hb
        obtain ⟨j, heq, hj⟩ := hb
        cases j using Fin.cases with
        | zero =>
            conv_lhs => rw [Fin.sum_univ_succ]
            conv_rhs => rw [Fin.sum_univ_succ]
            simp only [W, Fin.cons_zero, Fin.cons_succ]
            change a 0 * (t + 1) + t < b 0 * (t + 1) + ∑ i, b i.succ * w i
            have hstep : a 0 * (t + 1) + t < (a 0 + 1) * (t + 1) := by
              rw [Nat.add_mul, Nat.one_mul]
              omega
            have hmul : (a 0 + 1) * (t + 1) ≤ b 0 * (t + 1) :=
              Nat.mul_le_mul_right (t + 1) (Nat.succ_le_of_lt hj)
            exact (hstep.trans_le hmul).trans_le (Nat.le_add_right _ _)
        | succ j =>
            have hhead : a 0 = b 0 := heq 0 (by change 0 < j.val + 1; omega)
            have htail : (∑ i, a i.succ * w i) < ∑ i, b i.succ * w i := by
              apply hlex (fun i ↦ b i.succ)
              refine ⟨j, ?_, hj⟩
              intro i hi
              exact heq i.succ (by change i.val + 1 < j.val + 1; exact Nat.succ_lt_succ hi)
            conv_lhs => rw [Fin.sum_univ_succ]
            conv_rhs => rw [Fin.sum_univ_succ]
            simp only [W, Fin.cons_zero, Fin.cons_succ, hhead]
            exact Nat.add_lt_add_left htail _

/-- Positive integer weights with last weight one isolate a specified exponent
from all exponents lexicographically larger than it. -/
theorem exists_pos_weight_lt_of_lex_lt (n : ℕ) (a : Fin (n + 1) →₀ ℕ) :
    ∃ w : Fin (n + 1) → ℕ,
      (∀ i, 0 < w i) ∧ w (Fin.last n) = 1 ∧
      ∀ b : Fin (n + 1) →₀ ℕ,
        Finsupp.Lex (· < ·) (· < ·) a b → weight w a < weight w b := by
  obtain ⟨w, hw, hlast, hlex⟩ := exists_pos_lexWeight_aux n a
  refine ⟨w, hw, hlast, fun b hb ↦ ?_⟩
  simpa only [weight_eq_sum, smul_eq_mul] using hlex b (Finsupp.lex_def.mp hb)

end Finsupp
