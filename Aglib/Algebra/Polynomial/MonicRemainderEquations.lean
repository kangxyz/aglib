/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# Finite equations for divisibility by a monic polynomial

After any coefficient-ring specialization, divisibility by a fixed monic
polynomial is equivalent to vanishing of finitely many specialized remainder
coefficients. This is the finite-equation interface needed to descend formal
Weierstrass divisibility to an induction in one fewer variable. The degree
bound is on the universal monic divisor, so the same finite family works for
all specializations, including those to rings with zero divisors.
-/

@[expose] public section

namespace Polynomial

variable {R S : Type*} [Ring R] [Ring S]

/-- Divisibility after coefficient specialization is a finite system of
remainder-coefficient equations. The bound `d = 0` is allowed. -/
theorem map_dvd_iff_fin_coeff_modByMonic_eq_zero (φ : R →+* S)
    (p q : R[X]) (hq : q.Monic) (d : ℕ) (hd : q.degree ≤ d) :
    q.map φ ∣ p.map φ ↔ ∀ k : Fin d, φ ((p %ₘ q).coeff k) = 0 := by
  rw [← modByMonic_eq_zero_iff_dvd (hq.map φ), ← map_modByMonic φ hq]
  constructor
  · intro h k
    simpa only [coeff_map, coeff_zero] using congrArg (fun r : S[X] ↦ r.coeff k) h
  · intro h
    rw [← sum_modByMonic_coeff hq hd]
    simp only [Polynomial.map_sum, map_monomial, h, monomial_zero_right, Finset.sum_const_zero]

end Polynomial
