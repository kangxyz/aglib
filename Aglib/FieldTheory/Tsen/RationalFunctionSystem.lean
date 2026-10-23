/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Tsen.PolynomialCoordinates
public import Aglib.FieldTheory.Tsen.PolynomialSystem

/-!
# Homogeneous systems over the rational function field

A single polynomial clears every coefficient denominator of every equation.
The polynomial-system theorem then provides a nonzero rational solution.
-/

@[expose] public section

open scoped Polynomial

namespace MvPolynomial

/-- Simultaneous denominator clearing for a finite family of multivariate
polynomials over a rational-function field. -/
theorem exists_common_polynomial_denominator {K ι σ : Type*} [Field K] [Finite ι]
    (p : ι → MvPolynomial σ (RatFunc K)) :
    ∃ q : K[X], q ≠ 0 ∧ ∃ P : ι → MvPolynomial σ K[X],
      ∀ i, map (algebraMap K[X] (RatFunc K)) (P i) =
        C (algebraMap K[X] (RatFunc K) q) * p i := by
  classical
  let J := Σ i, ↥((p i).support)
  obtain ⟨q, hq, a, ha⟩ := RatFunc.exists_common_polynomial_denominator
    (fun j : J => (p j.1).coeff j.2)
  refine ⟨q, hq, fun i => ∑ e : (p i).support, monomial e.1 (a ⟨i, e⟩), ?_⟩
  intro i
  rw [map_sum]
  simp only [map_monomial, ha, ← C_mul_monomial, ← Finset.mul_sum]
  congr 1
  exact (Finset.sum_coe_sort (p i).support
    (fun e => monomial e ((p i).coeff e))).trans (p i).support_sum_monomial_coeff

/-- A system of degree-`d` forms over `K(T)` with more than `d` times as many
variables as equations has a nonzero solution when `K` is algebraically closed. -/
theorem exists_ratFunc_solution {K ι σ : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] [Fintype σ] (p : ι → MvPolynomial σ (RatFunc K))
    {d : ℕ} (hd : 0 < d) (hp : ∀ i, (p i).IsHomogeneous d)
    (hcard : Fintype.card ι * d < Fintype.card σ) :
    ∃ x : σ → RatFunc K, x ≠ 0 ∧ ∀ i, eval x (p i) = 0 := by
  obtain ⟨q, hq, P, hP⟩ := exists_common_polynomial_denominator p
  have hPh : ∀ i, (P i).IsHomogeneous d := by
    intro i
    apply IsHomogeneous.of_map (RatFunc.algebraMap_injective K)
    rw [hP]
    exact (hp i).C_mul _
  obtain ⟨x, hx, hpx⟩ := exists_polynomial_solution P hd hPh hcard
  refine ⟨(algebraMap K[X] (RatFunc K)) ∘ x, ?_, ?_⟩
  · intro h
    apply hx
    funext i
    apply RatFunc.algebraMap_injective
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun h i
  · intro i
    have h := congrArg (algebraMap K[X] (RatFunc K)) (hpx i)
    rw [map_eval, hP, eval_mul, eval_C, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left
      (by simpa only [map_zero] using (RatFunc.algebraMap_injective K).ne hq)

end MvPolynomial
