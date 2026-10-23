/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The degree estimate in Tsen's polynomial ansatz

Evaluating a degree-`d` homogeneous form whose polynomial coefficients have
degree at most `D`, at polynomials of degree at most `m`, gives degree at most
`D + d * m`. This estimate includes zero coefficients and zero coordinates.
-/

@[expose] public section

namespace MvPolynomial

open scoped Polynomial

/-- The exact linear-in-`m` degree estimate for homogeneous evaluation. -/
theorem IsHomogeneous.natDegree_eval_le {K σ : Type*} [CommSemiring K]
    {p : MvPolynomial σ K[X]} {d D m : ℕ} (hp : p.IsHomogeneous d)
    (hc : ∀ e ∈ p.support, (p.coeff e).natDegree ≤ D)
    (x : σ → K[X]) (hx : ∀ i, (x i).natDegree ≤ m) :
    (eval x p).natDegree ≤ D + d * m := by
  classical
  rw [p.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [eval_monomial]
  apply Polynomial.natDegree_mul_le.trans
  apply add_le_add (hc e he)
  rw [Finsupp.prod]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    ∑ i ∈ e.support, ((x i) ^ e i).natDegree ≤ ∑ i ∈ e.support, e i * m :=
      Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le_of_le _ (hx i)
    _ = d * m := by rw [← Finset.sum_mul, ← hp.degree_eq_sum_deg_support he]

end MvPolynomial
