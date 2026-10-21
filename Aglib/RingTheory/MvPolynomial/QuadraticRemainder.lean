/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Quadratic remainders at the origin

Polynomials in the square of the variable ideal have zero constant and
linear coefficients. Their values and first partial derivatives vanish at
the origin over arbitrary commutative rings. Adding constants and coordinates
therefore gives an identity evaluated Jacobian. No approximation theorem is
asserted here.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- A polynomial in the square of the variable ideal vanishes at the origin. -/
theorem eval_zero_eq_zero_of_mem_idealOfVars_sq {p : MvPolynomial σ R}
    (hp : p ∈ idealOfVars σ R ^ 2) : eval (0 : σ → R) p = 0 := by
  rw [eval_zero, constantCoeff_eq]
  exact (mem_pow_idealOfVars_iff' 2 p).mp hp 0 (by simp)

/-- A polynomial in the square of the variable ideal has zero first derivatives
at the origin, including over rings with positive characteristic or zero divisors. -/
theorem eval_zero_pderiv_eq_zero_of_mem_idealOfVars_sq {p : MvPolynomial σ R}
    (hp : p ∈ idealOfVars σ R ^ 2) (j : σ) :
    eval (0 : σ → R) (pderiv j p) = 0 := by
  classical
  have h := (mem_pow_idealOfVars_iff' 2 p).mp hp (Finsupp.single j 1) (by simp)
  simpa [eval_zero, constantCoeff_eq, coeff_pderiv] using h

/-- Adding a constant and the coordinate to quadratic remainders gives an
identity evaluated Jacobian. Rows index equations and columns index variables. -/
theorem eval_zero_pderiv_C_add_X_add [DecidableEq σ]
    (e : σ → R) (q : σ → MvPolynomial σ R)
    (hq : ∀ i, q i ∈ idealOfVars σ R ^ 2) (i j : σ) :
    eval (0 : σ → R) (pderiv j (C (e i) + X i + q i)) = if i = j then 1 else 0 := by
  simp only [map_add, pderiv_C, zero_add]
  rw [eval_zero_pderiv_eq_zero_of_mem_idealOfVars_sq (hq i) j, add_zero]
  simp [Pi.single_apply]

end MvPolynomial
