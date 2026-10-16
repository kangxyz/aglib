/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Evaluation of homogeneous polynomials

Scaling every variable by the same element multiplies the evaluation of a degree-`n`
homogeneous polynomial by the `n`th power of that element. The coefficient homomorphism is
arbitrary, and no finiteness of the variable type or invertibility of the scaling factor is needed.
-/

@[expose] public section

namespace MvPolynomial.IsHomogeneous

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S]
  {p : MvPolynomial ι R} {n : ℕ}

/-- Homogeneous evaluation commutes with a common multiplicative scaling of all variables. -/
theorem eval₂_mul (hp : p.IsHomogeneous n) (f : R →+* S) (v : ι → S) (c : S) :
    p.eval₂ f (fun i => c * v i) = c ^ n * p.eval₂ f v := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [eval₂_add, ihp, ihq, mul_add]
  | monomial d r hd =>
    have hdeg : d.degree = n := by
      simpa [Finsupp.degree_eq_weight_one, ← Pi.one_def] using hd
    simp only [eval₂_monomial, mul_pow, Finsupp.prod_mul]
    have hc : d.prod (fun _ k => c ^ k) = c ^ n := by
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdeg]
    rw [hc]
    ac_rfl

end MvPolynomial.IsHomogeneous
