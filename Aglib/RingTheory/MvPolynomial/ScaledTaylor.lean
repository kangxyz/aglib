/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.Ring

/-!
# Scaled first-order expansion of multivariate polynomials

For a polynomial over a commutative ring, evaluation at a point plus scaled
increments has its usual first-order term and a remainder in the square of
the ideal containing the increments. The identity retains the square of the
scale as an explicit factor and never cancels it.

The coefficient algebra and the scale may have zero divisors. The scale may
be zero, and the finite variable type may be empty. This is a polynomial
identity, not an implicit-function or Artin approximation theorem.
-/

@[expose] public section

namespace MvPolynomial

variable {R B σ : Type*} [CommRing R] [CommRing B] [Algebra R B] [Fintype σ]

/-- A scaled first-order expansion with a quadratic-ideal remainder.
No regularity or invertibility assumption is made on the scale. -/
theorem exists_scaled_firstOrder_remainder (p : MvPolynomial σ R)
    (y : σ → R) (d : R) (z : σ → B) (I : Ideal B)
    (hz : ∀ j, z j ∈ I) :
    ∃ q ∈ I ^ 2,
      aeval (fun j ↦ algebraMap R B (y j) + algebraMap R B d * z j) p =
        algebraMap R B (eval y p) +
          algebraMap R B d * (∑ j, algebraMap R B (eval y (pderiv j p)) * z j) +
          algebraMap R B (d ^ 2) * q := by
  classical
  let L : MvPolynomial σ R → B :=
    fun p ↦ ∑ j, algebraMap R B (eval y (pderiv j p)) * z j
  have hLmem (p : MvPolynomial σ R) : L p ∈ I := by
    exact I.sum_mem fun j _ ↦ I.mul_mem_left _ (hz j)
  have hLadd (p r : MvPolynomial σ R) : L (p + r) = L p + L r := by
    simp [L, map_add, add_mul, Finset.sum_add_distrib]
  have hLmulX (p : MvPolynomial σ R) (j : σ) :
      L (p * X j) = L p * algebraMap R B (y j) + algebraMap R B (eval y p) * z j := by
    have hterm (k : σ) :
        algebraMap R B (eval y (pderiv k (p * X j))) * z k =
          (algebraMap R B (eval y (pderiv k p)) * z k) * algebraMap R B (y j) +
            if j = k then algebraMap R B (eval y p) * z k else 0 := by
      by_cases h : j = k
      · subst k
        simp only [pderiv_mul, pderiv_X_self, mul_one,
          eval_X, map_add, map_mul, ite_true]
        ring
      · rw [pderiv_mul, pderiv_X_of_ne h]
        simp only [mul_zero, add_zero, eval_X, map_mul, ite_eq_right h]
        ring
    change (∑ k, algebraMap R B (eval y (pderiv k (p * X j))) * z k) = _
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, L]
  change ∃ q ∈ I ^ 2,
    aeval (fun j ↦ algebraMap R B (y j) + algebraMap R B d * z j) p =
      algebraMap R B (eval y p) + algebraMap R B d * L p +
        algebraMap R B (d ^ 2) * q
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, (I ^ 2).zero_mem, ?_⟩
      simp [L]
  | add p r hp hr =>
      obtain ⟨q, hq, hp⟩ := hp
      obtain ⟨s, hs, hr⟩ := hr
      refine ⟨q + s, (I ^ 2).add_mem hq hs, ?_⟩
      rw [map_add, hp, hr, eval_add, map_add, hLadd]
      ring
  | mul_X p j hp =>
      obtain ⟨q, hq, hp⟩ := hp
      refine ⟨q * algebraMap R B (y j) + L p * z j +
        algebraMap R B d * q * z j, ?_, ?_⟩
      · apply (I ^ 2).add_mem
        · apply (I ^ 2).add_mem
          · exact (I ^ 2).mul_mem_right _ hq
          · simpa only [pow_two] using Ideal.mul_mem_mul (hLmem p) (hz j)
        · exact (I ^ 2).mul_mem_right _ ((I ^ 2).mul_mem_left _ hq)
      · rw [map_mul, hp, aeval_X, eval_mul, eval_X, map_mul, hLmulX, map_pow]
        ring

end MvPolynomial
