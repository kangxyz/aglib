/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Binomial

/-! Focused consumer of the integer facts about `Ring.choose`. -/

@[expose] public section

/-- Pascal's rule in difference form. -/
example (x : ℤ) (i : ℕ) :
    Ring.choose x (i + 1) - Ring.choose (x - 1) (i + 1) = Ring.choose (x - 1) i :=
  Ring.choose_succ_sub_choose_pred x i

/-- `0 ≤ C(y, i) ≤ yⁱ` and `-a C(y, i) ≤ a² yⁱ` for `y ≥ 0`. -/
example (a y : ℤ) (hy : 0 ≤ y) (i : ℕ) :
    (0 ≤ Ring.choose y i ∧ Ring.choose y i ≤ y ^ i) ∧ -(a * Ring.choose y i) ≤ a ^ 2 * y ^ i :=
  ⟨Ring.choose_nonneg_le_pow hy i, Ring.neg_mul_choose_le a hy i⟩

/-- A function with a binomial forward difference is a binomial sum. -/
example (f : ℤ → ℤ) (N : ℕ) (b : Fin N → ℤ)
    (h : ∀ m : ℤ, f (m + 1) - f m = ∑ i : Fin N, b i * Ring.choose m i) :
    ∃ a : Fin (N + 1) → ℤ, ∀ m : ℤ, f m = ∑ i : Fin (N + 1), a i * Ring.choose m i :=
  ⟨_, Int.eq_sum_choose_of_fwdDiff b h⟩

/-- The binomial sum is exact on a constant function: `a₀ = c` and no higher term. -/
example (c : ℤ) (m : ℤ) :
    (fun _ : ℤ => c) m = ∑ i : Fin 1, (Fin.cons c Fin.elim0 : Fin 1 → ℤ) i * Ring.choose m i :=
  Int.eq_sum_choose_of_fwdDiff (f := fun _ => c) Fin.elim0 (fun _ => by simp) m

/--
info: 'Ring.choose_succ_sub_choose_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ring.choose_succ_sub_choose_pred

/--
info: 'Ring.choose_nonneg_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ring.choose_nonneg_le_pow

/--
info: 'Ring.neg_mul_choose_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ring.neg_mul_choose_le

/--
info: 'Int.eq_sum_choose_of_fwdDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Int.eq_sum_choose_of_fwdDiff
