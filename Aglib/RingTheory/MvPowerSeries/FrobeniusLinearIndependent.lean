/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.RingTheory.MvPolynomial.FrobeniusDecomposition
public import Aglib.RingTheory.MvPowerSeries.FrobeniusCoefficients
public import Mathlib.Algebra.CharP.Algebra

/-!
# Polynomial-linear Frobenius independence of series

Finite polynomial Frobenius decomposition and coefficient independence combine
to preserve finite polynomial-linear independence under Frobenius.
-/

@[expose] public noncomputable section

namespace MvPowerSeries

/-- Finite polynomial-linear independence of series survives Frobenius.
This intermediate statement needs no rational-function action on the series ring. -/
lemma linearIndependent_pow_over_mvPolynomial
    {k σ ι : Type*} [Field k] [Finite ι]
    (p : ℕ) (hp : p ≠ 0) [ExpChar k p]
    (f : ι → MvPowerSeries σ k)
    (hf : LinearIndependent (MvPolynomial σ k) f) :
    LinearIndependent (MvPolynomial σ k) (fun i => f i ^ p) := by
  classical
  let := Fintype.ofFinite ι
  let m : MvPolynomial σ k →+* MvPowerSeries σ k := MvPolynomial.coeToMvPowerSeries.ringHom
  have hm (q : MvPolynomial σ k) :
      algebraMap (MvPolynomial σ k) (MvPowerSeries σ k) q = m q := by
    simp [m, algebraMap_apply']
  have hmmono (e : σ →₀ ℕ) (a : k) :
      m (MvPolynomial.monomial e a) = monomial e a :=
    MvPolynomial.coe_monomial e a
  let : ExpChar (MvPowerSeries σ k) p := expChar_of_injective_ringHom (MvPowerSeries.C_injective) p
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  obtain ⟨b, r, hb, hr, Q, hQ⟩ :=
    MvPolynomial.exists_polynomial_frobenius_decomposition p hp c
  let g (e : r) (j : b) : MvPowerSeries σ k := ∑ i, m (Q i j e) * f i
  have hrel : ∑ e : r, ∑ j : b,
      monomial (e : σ →₀ ℕ) (j : k) * g e j ^ p = 0 := by
    let A (e : r) (j : b) (i : ι) : MvPowerSeries σ k :=
      monomial (e : σ →₀ ℕ) (j : k) * (m (Q i j e) * f i) ^ p
    calc
      _ = ∑ e : r, ∑ j : b, ∑ i, A e j i := by
        simp only [g, A, sum_pow_char p, Finset.mul_sum]
      _ = ∑ e : r, ∑ i, ∑ j : b, A e j i := by
        apply Finset.sum_congr rfl
        intro e he
        exact Finset.sum_comm
      _ = ∑ i, ∑ e : r, ∑ j : b, A e j i := Finset.sum_comm
      _ = ∑ i, m (c i) * f i ^ p := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hQ i, map_sum]
        simp only [A, map_sum, map_mul, map_pow, Finset.sum_mul, mul_pow, mul_assoc,
          hmmono]
      _ = 0 := by simpa only [Algebra.smul_def, hm] using hc
  have hg := sum_monomial_mul_pow_eq_zero p hp hb
    (fun e : r => (e : σ →₀ ℕ)) (fun e x => hr e e.property x)
    Subtype.val_injective g hrel
  have hQ0 (i : ι) (j : b) (e : r) : Q i j e = 0 := by
    apply Fintype.linearIndependent_iff.mp hf (fun i => Q i j e) _ i
    simpa only [g, Algebra.smul_def, hm] using hg e j
  intro i
  rw [hQ i]
  simp only [hQ0, zero_pow hp, mul_zero, Finset.sum_const_zero]

end MvPowerSeries
