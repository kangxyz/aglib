/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Integer functions given by rational polynomials

An integer function `f : ℤ → ℤ` is given by a rational polynomial when some `Φ : ℚ[X]`
satisfies `f m = Φ(m)` for every integer `m`, negative integers included. If the forward
difference `m ↦ f (m + 1) - f m` is given by a rational polynomial, so is `f`. The discrete
antiderivative comes from Bernoulli polynomials, `B_{p+1}(1 + x) = B_{p+1}(x) + (p + 1) x ^ p`
(`Polynomial.bernoulli_eval_one_add`).

This is the numerical step of the Hilbert polynomial induction on projective space.
-/

@[expose] public section

noncomputable section

namespace Polynomial

/-- An integer function is given by a rational polynomial at every integer. -/
def IsPolynomialOnInt (f : ℤ → ℤ) : Prop :=
  ∃ Φ : ℚ[X], ∀ m : ℤ, (f m : ℚ) = Φ.eval (m : ℚ)

/-- Every rational polynomial has a discrete antiderivative. -/
theorem exists_eval_add_one_sub_eval (P : ℚ[X]) :
    ∃ Q : ℚ[X], ∀ x : ℚ, Q.eval (x + 1) - Q.eval x = P.eval x := by
  refine ⟨∑ p ∈ Finset.range (P.natDegree + 1),
    C (P.coeff p / ((p : ℚ) + 1)) * bernoulli (p + 1), fun x => ?_⟩
  rw [P.eval_eq_sum_range, eval_finsetSum, eval_finsetSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [eval_mul, eval_C]
  rw [add_comm x 1, bernoulli_eval_one_add, Nat.add_sub_cancel]
  have hp : (p : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

namespace IsPolynomialOnInt

/-- Constant functions are given by constant polynomials. -/
theorem const (c : ℤ) : IsPolynomialOnInt fun _ => c :=
  ⟨C (c : ℚ), fun _ => by simp⟩

/-- The polynomial property is invariant under pointwise equality. -/
theorem congr {f g : ℤ → ℤ} (hf : IsPolynomialOnInt f) (h : ∀ m, f m = g m) :
    IsPolynomialOnInt g := by
  obtain ⟨Φ, hΦ⟩ := hf
  exact ⟨Φ, fun m => by rw [← h m, hΦ m]⟩

/-- Sums of polynomial functions are polynomial. -/
theorem add {f g : ℤ → ℤ} (hf : IsPolynomialOnInt f) (hg : IsPolynomialOnInt g) :
    IsPolynomialOnInt fun m => f m + g m := by
  obtain ⟨Φ, hΦ⟩ := hf
  obtain ⟨Ψ, hΨ⟩ := hg
  exact ⟨Φ + Ψ, fun m => by rw [eval_add, ← hΦ m, ← hΨ m]; push_cast; ring⟩

/-- Differences of polynomial functions are polynomial. -/
theorem sub {f g : ℤ → ℤ} (hf : IsPolynomialOnInt f) (hg : IsPolynomialOnInt g) :
    IsPolynomialOnInt fun m => f m - g m := by
  obtain ⟨Φ, hΦ⟩ := hf
  obtain ⟨Ψ, hΨ⟩ := hg
  exact ⟨Φ - Ψ, fun m => by rw [eval_sub, ← hΦ m, ← hΨ m]; push_cast; ring⟩

/-- Integer translates of polynomial functions are polynomial. -/
theorem comp_add {f : ℤ → ℤ} (hf : IsPolynomialOnInt f) (c : ℤ) :
    IsPolynomialOnInt fun m => f (m + c) := by
  obtain ⟨Φ, hΦ⟩ := hf
  refine ⟨Φ.comp (X + C (c : ℚ)), fun m => ?_⟩
  rw [hΦ (m + c), eval_comp, eval_add, eval_X, eval_C]
  push_cast
  rfl

/-- If the forward difference of an integer function is polynomial, so is the function. The
hypothesis is Mathlib's `fwdDiff 1 f`, written out. -/
theorem of_fwdDiff {f : ℤ → ℤ} (h : IsPolynomialOnInt fun m => f (m + 1) - f m) :
    IsPolynomialOnInt f := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨Q, hQ⟩ := exists_eval_add_one_sub_eval P
  have hstep (m : ℤ) : (f (m + 1) : ℚ) - Q.eval ((m + 1 : ℤ) : ℚ) =
      (f m : ℚ) - Q.eval (m : ℚ) := by
    have h1 := hP m
    have h2 := hQ (m : ℚ)
    push_cast at h1 ⊢
    linarith
  have hconst (m : ℤ) : (f m : ℚ) - Q.eval (m : ℚ) = (f 0 : ℚ) - Q.eval 0 := by
    induction m using Int.induction_on with
    | zero => simp
    | succ k ih => rw [hstep, ih]
    | pred k ih =>
      have hk := hstep (-(k : ℤ) - 1)
      rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at hk
      rw [← hk, ih]
  refine ⟨Q + C ((f 0 : ℚ) - Q.eval 0), fun m => ?_⟩
  rw [eval_add, eval_C]
  linarith [hconst m]

/-- A rational polynomial agreeing with an integer function at every integer is unique. -/
theorem eq_of_eval {f : ℤ → ℤ} {Φ Ψ : ℚ[X]} (hΦ : ∀ m : ℤ, (f m : ℚ) = Φ.eval (m : ℚ))
    (hΨ : ∀ m : ℤ, (f m : ℚ) = Ψ.eval (m : ℚ)) : Φ = Ψ := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ))
  · rintro _ ⟨m, rfl⟩
    exact (hΦ m).symm.trans (hΨ m)
  · exact Set.infinite_range_of_injective Int.cast_injective

end IsPolynomialOnInt

open Classical in
/-- The rational polynomial of an integer function given by one, and `0` otherwise. -/
noncomputable def polynomialOnInt (f : ℤ → ℤ) : ℚ[X] :=
  if h : IsPolynomialOnInt f then Classical.choose h else 0

namespace IsPolynomialOnInt

/-- The chosen polynomial agrees with the function at every integer. -/
theorem eval_polynomialOnInt {f : ℤ → ℤ} (h : IsPolynomialOnInt f) (m : ℤ) :
    (f m : ℚ) = (polynomialOnInt f).eval (m : ℚ) := by
  unfold polynomialOnInt
  split_ifs
  exact Classical.choose_spec h m

/-- The chosen polynomial is the unique polynomial agreeing with the function. -/
theorem polynomialOnInt_eq {f : ℤ → ℤ} {Φ : ℚ[X]} (hΦ : ∀ m : ℤ, (f m : ℚ) = Φ.eval (m : ℚ)) :
    polynomialOnInt f = Φ :=
  eq_of_eval (eval_polynomialOnInt ⟨Φ, hΦ⟩) hΦ

end IsPolynomialOnInt

end Polynomial
