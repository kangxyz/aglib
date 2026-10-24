/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.Data.Finset.Max

/-!
# Coefficient products over normal domains

A nonzero polynomial in an integral domain algebra divides the image of a
nonzero polynomial over the base. Separately, if a product of two polynomials
over a field has coefficients in a subring integrally closed in that same
field, every product of individual coefficients belongs to the subring.

The latter assertion is proved in each valuation overring, using a coefficient
of maximal valuation to normalize each factor, and then by intersection of
valuation overrings (Stacks, Tag 090P). Over a normal local domain, a product
whose coefficient ideal is the unit ideal therefore makes an original
coefficient of either factor a generator of its coefficient ideal.
-/

@[expose] public section

noncomputable section

namespace Polynomial

section Integral

variable {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra.IsIntegral R S]

attribute [local instance] Polynomial.algebra

/-- A nonzero polynomial in an integral domain algebra divides the image of
a nonzero polynomial over the original base. The quotient is also nonzero. -/
theorem exists_nonzero_map_eq_mul_of_integral
    (hinj : Function.Injective (algebraMap R S)) {p : S[X]} (hp : p ≠ 0) :
    ∃ (F : R[X]) (Q : S[X]),
      F ≠ 0 ∧ Q ≠ 0 ∧ F.map (algebraMap R S) = p * Q := by
  have hpint : IsIntegral R[X] p :=
    Polynomial.isIntegral_iff_isIntegral_coeff.mpr
      (fun n ↦ Algebra.IsIntegral.isIntegral (p.coeff n))
  have hI : (Ideal.span ({p} : Set S[X])).under R[X] ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hp
      (Ideal.subset_span (Set.mem_singleton p)) hpint
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).mp hI
  change F.map (algebraMap R S) ∈ Ideal.span ({p} : Set S[X]) at hF
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp hF
  refine ⟨F, Q, hF0, ?_, hQ⟩
  intro hQ0
  apply hF0
  apply Polynomial.map_injective (algebraMap R S) hinj
  simp only [hQ, hQ0, mul_zero, Polynomial.map_zero]

end Integral

section Valuation

variable {K : Type*} [Field K]

private theorem scalar_mem_of_contentIdeal_eq_top (R : Subring K)
    (p : R[X]) (hp : p.contentIdeal = ⊤) (a : K)
    (hcoeff : ∀ n, a * (p.coeff n : K) ∈ R) : a ∈ R := by
  have hspan (x : R) (hx : x ∈ p.contentIdeal) : a * (x : K) ∈ R := by
    rw [contentIdeal_def] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hcoeff n
    | zero =>
      simpa only [ZeroMemClass.coe_zero, mul_zero] using R.zero_mem
    | add x y _ _ hx hy =>
      change a * ((x : K) + (y : K)) ∈ R
      rw [mul_add]
      exact R.add_mem hx hy
    | smul c x _ hx =>
      change a * ((c : K) * (x : K)) ∈ R
      rw [mul_left_comm]
      exact R.mul_mem c.property hx
  have h1 : (1 : R) ∈ p.contentIdeal := by rw [hp]; trivial
  simpa only [OneMemClass.coe_one, mul_one] using hspan 1 h1

private theorem exists_valuation_polynomial_normalization
    (V : ValuationSubring K) (p : K[X]) (hp : p ≠ 0) :
    ∃ (i : ℕ) (q : V.toSubring[X]),
      p.coeff i ≠ 0 ∧ q.coeff i = 1 ∧
        p = C (p.coeff i) * q.map V.toSubring.subtype := by
  classical
  obtain ⟨i, hi, hmax⟩ :=
    p.support.exists_max_image (fun n ↦ V.valuation (p.coeff n))
      (Polynomial.support_nonempty.mpr hp)
  have hi0 : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  let q : K[X] := C (p.coeff i)⁻¹ * p
  have hq (n : ℕ) : q.coeff n ∈ V.toSubring := by
    have hle : V.valuation (p.coeff n) ≤ V.valuation (p.coeff i) := by
      by_cases hn : p.coeff n = 0
      · simp only [hn, map_zero]; exact zero_le
      · exact hmax n (Polynomial.mem_support_iff.mpr hn)
    obtain ⟨c, hc⟩ := (V.valuation_le_iff (p.coeff n) (p.coeff i)).mp hle
    have he : (p.coeff i)⁻¹ * p.coeff n = (c : K) := by
      rw [← hc]
      simp only [mul_left_comm, inv_mul_cancel₀ hi0, mul_one]
    change (C (p.coeff i)⁻¹ * p).coeff n ∈ V.toSubring
    rw [coeff_C_mul, he]
    exact c.property
  have hqcoeff : (q.coeffs : Set K) ⊆ V.toSubring := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact hq n
  let qV : V.toSubring[X] := q.toSubring V.toSubring hqcoeff
  have hmap : qV.map V.toSubring.subtype = q := Polynomial.map_toSubring ..
  refine ⟨i, qV, hi0, ?_, ?_⟩
  · apply Subtype.ext
    change ((qV.coeff i : V.toSubring) : K) = 1
    simp only [qV, Polynomial.coeff_toSubring, q, coeff_C_mul, inv_mul_cancel₀ hi0]
  · rw [hmap]
    change p = C (p.coeff i) * (C (p.coeff i)⁻¹ * p)
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hi0, C_1, one_mul]

private theorem valuation_coeff_mul_coeff_mem
    (V : ValuationSubring K) (p q : K[X])
    (hpq : ∀ n, (p * q).coeff n ∈ V.toSubring) (i j : ℕ) :
    p.coeff i * q.coeff j ∈ V.toSubring := by
  by_cases hp : p = 0
  · simp only [hp, coeff_zero, zero_mul]; exact V.toSubring.zero_mem
  by_cases hq : q = 0
  · simp only [hq, coeff_zero, mul_zero]; exact V.toSubring.zero_mem
  obtain ⟨a, pV, _, hpV, hpm⟩ := exists_valuation_polynomial_normalization V p hp
  obtain ⟨b, qV, _, hqV, hqm⟩ := exists_valuation_polynomial_normalization V q hq
  have hpc : pV.contentIdeal = ⊤ := by
    apply pV.contentIdeal.eq_top_iff_one.mpr
    rw [← hpV]
    exact pV.coeff_mem_contentIdeal a
  have hqc : qV.contentIdeal = ⊤ := by
    apply qV.contentIdeal.eq_top_iff_one.mpr
    rw [← hqV]
    exact qV.coeff_mem_contentIdeal b
  have hprod :
      p * q = C (p.coeff a * q.coeff b) * (pV * qV).map V.toSubring.subtype := by
    calc
      p * q =
          (C (p.coeff a) * pV.map V.toSubring.subtype) *
            (C (q.coeff b) * qV.map V.toSubring.subtype) :=
        congrArg₂ (· * ·) hpm hqm
      _ = C (p.coeff a * q.coeff b) * (pV * qV).map V.toSubring.subtype := by
        rw [Polynomial.map_mul, C_mul]
        ring
  have hab : p.coeff a * q.coeff b ∈ V.toSubring :=
    scalar_mem_of_contentIdeal_eq_top V.toSubring (pV * qV)
      (contentIdeal_mul_eq_top_of_contentIdeal_eq_top hpc hqc)
      (p.coeff a * q.coeff b) (fun n ↦ by
        have hn := hpq n
        rwa [hprod, coeff_C_mul, coeff_map] at hn)
  have hpi : p.coeff i = p.coeff a * (pV.coeff i : K) := by
    simpa only [coeff_C_mul, coeff_map, Subring.subtype_apply,
      ValuationSubring.subtype_apply] using
      congrArg (fun f : K[X] ↦ f.coeff i) hpm
  have hqj : q.coeff j = q.coeff b * (qV.coeff j : K) := by
    simpa only [coeff_C_mul, coeff_map, Subring.subtype_apply,
      ValuationSubring.subtype_apply] using
      congrArg (fun f : K[X] ↦ f.coeff j) hqm
  rw [hpi, hqj]
  rw [mul_mul_mul_comm]
  exact V.toSubring.mul_mem hab
    (V.toSubring.mul_mem (pV.coeff i).property (qV.coeff j).property)

end Valuation

end Polynomial

namespace Subring

variable {K : Type*} [Field K]

/-- If a polynomial product has coefficients in a subring integrally closed
in the same field, each product of coefficients lies in that subring. -/
theorem coeff_mul_coeff_mem_of_coeff_mul_mem
    (R : Subring K) [IsIntegrallyClosedIn R K] (p q : Polynomial K)
    (hpq : ∀ n, (p * q).coeff n ∈ R) (i j : ℕ) :
    p.coeff i * q.coeff j ∈ R := by
  by_contra h
  obtain ⟨V, hRV, hnot⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn h
  exact hnot (Polynomial.valuation_coeff_mul_coeff_mem V p q
    (fun n ↦ hRV (hpq n)) i j)

end Subring

namespace Polynomial

section IntegralCoefficients

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- Integral coefficients of a product imply integrality of every
cross-product of coefficients, all in the original field. -/
theorem isIntegral_coeff_mul_coeff (p q : K[X])
    (hpq : ∀ n, IsIntegral R ((p * q).coeff n)) (i j : ℕ) :
    IsIntegral R (p.coeff i * q.coeff j) := by
  exact Subring.coeff_mul_coeff_mem_of_coeff_mul_mem
    (integralClosure R K).toSubring p q hpq i j

variable [IsFractionRing R K] [IsIntegrallyClosed R]

/-- Normality in the specified fraction field makes every cross-product an
element of the original coefficient-ring image. -/
theorem exists_algebraMap_eq_coeff_mul_coeff (p q : K[X])
    (hpq : ∀ n, ∃ r : R, algebraMap R K r = (p * q).coeff n) (i j : ℕ) :
    ∃ r : R, algebraMap R K r = p.coeff i * q.coeff j := by
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_coeff_mul_coeff p q
  intro n
  obtain ⟨r, hr⟩ := hpq n
  rw [← hr]
  exact isIntegral_algebraMap

end IntegralCoefficients

section Local

variable {R K : Type*} [CommRing R] [IsLocalRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- A product with unit coefficient ideal over a normal local domain makes
one original nonzero coefficient of its integral factor a generator.
The witnesses give both literal divisibility and the original field ratios. -/
theorem exists_coeff_generator_of_contentIdeal_eq_top
    (p : R[X]) (q : K[X]) (F : R[X])
    (hF : F.map (algebraMap R K) = p.map (algebraMap R K) * q)
    (hcontent : F.contentIdeal = ⊤) :
    ∃ i : ℕ, p.coeff i ≠ 0 ∧
      p.contentIdeal = Ideal.span ({p.coeff i} : Set R) ∧
      ∀ k : ℕ, ∃ r : R, p.coeff k = p.coeff i * r ∧
        algebraMap R K r =
          algebraMap R K (p.coeff k) / algebraMap R K (p.coeff i) := by
  classical
  have hcross (i j : ℕ) :
      ∃ r : R, algebraMap R K r = algebraMap R K (p.coeff i) * q.coeff j := by
    simpa only [coeff_map] using
      exists_algebraMap_eq_coeff_mul_coeff (p.map (algebraMap R K)) q
        (fun n ↦ ⟨F.coeff n, by
          simpa only [coeff_map] using congrArg (fun f : K[X] ↦ f.coeff n) hF⟩) i j
  choose c hc using hcross
  have hcoeff (n : ℕ) :
      F.coeff n = ∑ ij ∈ Finset.antidiagonal n, c ij.1 ij.2 := by
    apply IsFractionRing.injective R K
    calc
      algebraMap R K (F.coeff n) =
          (F.map (algebraMap R K)).coeff n := (coeff_map ..).symm
      _ = (p.map (algebraMap R K) * q).coeff n := congrArg (fun f ↦ f.coeff n) hF
      _ = ∑ ij ∈ Finset.antidiagonal n,
          algebraMap R K (p.coeff ij.1) * q.coeff ij.2 := by
        rw [coeff_mul]
        simp only [coeff_map]
      _ = algebraMap R K (∑ ij ∈ Finset.antidiagonal n, c ij.1 ij.2) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun ij _ ↦ (hc ij.1 ij.2).symm)
  have hunit : ∃ i j, IsUnit (c i j) := by
    by_contra! hnone
    have hle : F.contentIdeal ≤ IsLocalRing.maximalIdeal R := by
      rw [contentIdeal_def, Ideal.span_le]
      intro x hx
      obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      rw [hcoeff]
      apply Ideal.sum_mem
      intro ij _
      change ¬ IsUnit (c ij.1 ij.2)
      exact hnone ij.1 ij.2
    rw [hcontent] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_unique hle)
  obtain ⟨i, j, hij⟩ := hunit
  obtain ⟨d, hd⟩ := hij.exists_right_inv
  have hiK : algebraMap R K (p.coeff i) ≠ 0 := by
    intro hi
    have hz : algebraMap R K (c i j) = 0 := by rw [hc, hi, zero_mul]
    exact (hij.map (algebraMap R K)).ne_zero hz
  have hi : p.coeff i ≠ 0 := by
    intro hi
    apply hiK
    simp only [hi, map_zero]
  have hdiv (k : ℕ) : p.coeff i * (c k j * d) = p.coeff k := by
    apply IsFractionRing.injective R K
    calc
      algebraMap R K (p.coeff i * (c k j * d)) =
          algebraMap R K (p.coeff i) *
            (algebraMap R K (c k j) * algebraMap R K d) := by simp only [map_mul]
      _ = algebraMap R K (p.coeff k) *
          (algebraMap R K (c i j) * algebraMap R K d) := by
        rw [hc k j, hc i j]
        ring
      _ = algebraMap R K (p.coeff k) := by
        rw [← map_mul, hd, map_one, mul_one]
  refine ⟨i, hi, le_antisymm ?_ ?_, fun k ↦ ⟨c k j * d, (hdiv k).symm, ?_⟩⟩
  · rw [contentIdeal_def, Ideal.span_le]
    intro x hx
    obtain ⟨k, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact Ideal.mem_span_singleton.mpr ⟨c k j * d, (hdiv k).symm⟩
  · exact Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr (p.coeff_mem_contentIdeal i))
  · apply (eq_div_iff hiK).mpr
    rw [mul_comm, ← map_mul, hdiv]

end Local

end Polynomial
