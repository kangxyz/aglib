/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.QuotientDensity
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Polynomial approximation from finite coefficient quotients

Surjectivity on a coefficient-ring quotient supplies polynomial approximations
in the source ring, not merely in the completed coefficient ring. The error
is measured in the mixed maximal ideal of the full power-series ring.
This is a finite-quotient consumer; it asserts no Artin approximation property.
-/

@[expose] public section

namespace PowerSeries

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]

/-- Finite coefficient-quotient surjectivity gives source-polynomial approximation
with respect to the mixed maximal ideal. -/
theorem exists_polynomial_map_sub_mem_maximalIdeal_pow
    (φ : A →+* B) (c : ℕ)
    (hφ : Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ c)).comp φ))
    (f : PowerSeries B) :
    ∃ p : Polynomial A, (p.map φ : PowerSeries B) - f ∈
      IsLocalRing.maximalIdeal (PowerSeries B) ^ c := by
  classical
  let m := IsLocalRing.maximalIdeal B
  let n := IsLocalRing.maximalIdeal (PowerSeries B)
  have hC : m.map (C : B →+* PowerSeries B) ≤ n := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change C b ∈ n
    simpa only [n, m, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_constantCoeff, constantCoeff_C] using hb
  have hCpow : (m ^ c).map (C : B →+* PowerSeries B) ≤ n ^ c := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hC c
  have hX : (X : PowerSeries B) ∈ n := by
    simp only [n, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_constantCoeff, constantCoeff_X, not_isUnit_zero, not_false_eq_true]
  have hb (j : ℕ) : ∃ b : A, φ b - coeff j f ∈ m ^ c := by
    obtain ⟨b, hb⟩ := hφ (Ideal.Quotient.mk (m ^ c) (coeff j f))
    exact ⟨b, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hb⟩
  choose b hb using hb
  let p : Polynomial A := ∑ j : Fin c, Polynomial.C (b j) * Polynomial.X ^ (j : ℕ)
  have htrunc : (∑ j : Fin c,
      Polynomial.C (coeff j f) * Polynomial.X ^ (j : ℕ)) = trunc c f := by
    have h := (Polynomial.sum_fin (fun i a ↦ Polynomial.C a * Polynomial.X ^ i)
      (by simp) (degree_trunc_lt f c)).trans (Polynomial.sum_C_mul_X_pow_eq (trunc c f))
    simpa only [coeff_trunc, Fin.is_lt, ite_true] using h
  have hsum (v : Fin c → Polynomial B) :
      ((∑ j, v j : Polynomial B) : PowerSeries B) = ∑ j, (v j : PowerSeries B) :=
    map_sum Polynomial.coeToPowerSeries.ringHom v Finset.univ
  have hdiff : (p.map φ : PowerSeries B) - (trunc c f : PowerSeries B) =
      ∑ j : Fin c, C (φ (b j) - coeff j f) * X ^ (j : ℕ) := by
    rw [← htrunc]
    simp only [p, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, hsum, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_sub, sub_mul]
  have hhead : (p.map φ : PowerSeries B) - (trunc c f : PowerSeries B) ∈ n ^ c := by
    rw [hdiff]
    apply Ideal.sum_mem
    intro j _
    exact Ideal.mul_mem_right _ _ (hCpow (Ideal.mem_map_of_mem C (hb j)))
  have htail : (X : PowerSeries B) ^ c ∣ f - (trunc c f : PowerSeries B) := by
    rw [X_pow_dvd_iff]
    intro j hj
    simp only [map_sub, Polynomial.coeff_coe, coeff_trunc, hj, ite_true, sub_self]
  have htailmem : f - (trunc c f : PowerSeries B) ∈ n ^ c := by
    obtain ⟨q, hq⟩ := htail
    rw [hq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hX c)
  refine ⟨p, ?_⟩
  have h := (n ^ c).sub_mem hhead htailmem
  simpa only [sub_sub_sub_cancel_right] using h

/-- The actual adic completion supplies the finite-quotient hypothesis. -/
theorem exists_polynomial_map_sub_mem_maximalIdeal_pow_adicCompletion
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (c : ℕ) (f : PowerSeries (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    ∃ p : Polynomial R,
      (p.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
        PowerSeries (AdicCompletion (IsLocalRing.maximalIdeal R) R)) - f ∈
      IsLocalRing.maximalIdeal
        (PowerSeries (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ^ c :=
  exists_polynomial_map_sub_mem_maximalIdeal_pow _ c
    (AdicCompletion.quotient_maximalIdeal_pow_algebraMap_surjective R c) f

end PowerSeries
