/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Norm.Basic

/-!
# Uniformizer binomials over an actual DVR fraction field

The polynomial `X ^ e - C c`, for an actual DVR uniformizer `c` and positive
`e`, is Eisenstein. Gauss's lemma transports irreducibility to the actual
fraction field, so an actual root has precisely this minimal polynomial.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A uniformizer binomial is Eisenstein at the actual maximal ideal. -/
theorem uniformizer_binomial_isEisensteinAt {c : R} (hc : Irreducible c)
    (e : ℕ) (he : 0 < e) :
    (X ^ e - C c).IsEisensteinAt (maximalIdeal R) := by
  have hmonic := monic_X_pow_sub_C c (Nat.ne_of_gt he)
  have hc_mem : c ∈ maximalIdeal R := by
    rw [hc.maximalIdeal_eq]
    exact Ideal.subset_span (by simp)
  have hc_notMem : c ∉ maximalIdeal R ^ 2 := by
    rw [hc.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have hd : c ∣ (1 : R) := (mul_dvd_mul_iff_left hc.ne_zero).mp (by
      simpa only [pow_two, mul_one] using h)
    exact hc.not_isUnit (isUnit_of_dvd_one hd)
  refine ⟨?_, ?_, ?_⟩
  · rw [hmonic.leadingCoeff]
    exact Ideal.one_notMem _
  · intro n hn
    rw [natDegree_X_pow_sub_C] at hn
    by_cases hn0 : n = 0
    · subst n
      simpa [coeff_sub, coeff_X_pow, coeff_C, Nat.ne_of_gt he, (Nat.ne_of_gt he).symm] using
        (maximalIdeal R).neg_mem hc_mem
    · simp [coeff_sub, coeff_X_pow, coeff_C, hn0, ne_of_lt hn]
  · have hneg : -c ∉ maximalIdeal R ^ 2 := by
      simpa only [neg_mem_iff] using hc_notMem
    simpa [coeff_sub, coeff_X_pow, coeff_C, Nat.ne_of_gt he, (Nat.ne_of_gt he).symm]
      using hneg

/-- The irreducibility statement is valid for every positive exponent, with no
separability or residue-characteristic assumption. -/
theorem uniformizer_binomial_irreducible {c : R} (hc : Irreducible c)
    (e : ℕ) (he : 0 < e) : Irreducible (X ^ e - C c) := by
  exact (uniformizer_binomial_isEisensteinAt hc e he).irreducible inferInstance
    (monic_X_pow_sub_C c (Nat.ne_of_gt he)).isPrimitive (by
      simpa only [natDegree_X_pow_sub_C] using he)

variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- Gauss transport uses the literal fraction-field algebra map. -/
theorem uniformizer_binomial_irreducible_fraction {c : R} (hc : Irreducible c)
    (e : ℕ) (he : 0 < e) :
    Irreducible (X ^ e - C (algebraMap R F c)) := by
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C] using
    (monic_X_pow_sub_C c (Nat.ne_of_gt he)).irreducible_iff_irreducible_map_fraction_map
      (K := F) |>.mp (uniformizer_binomial_irreducible hc e he)

/-- An actual root therefore has the actual uniformizer binomial as minpoly. -/
theorem minpoly_eq_uniformizer_binomial
    {E : Type*} [Field E] [Algebra F E] {c : R} (hc : Irreducible c)
    (e : ℕ) (he : 0 < e) (θ : E)
    (hθ : θ ^ e = algebraMap F E (algebraMap R F c)) :
    minpoly F θ = X ^ e - C (algebraMap R F c) := by
  symm
  exact minpoly.eq_of_irreducible_of_monic
    (uniformizer_binomial_irreducible_fraction F hc e he)
    (by simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hθ)
    (monic_X_pow_sub_C _ (Nat.ne_of_gt he))

/-- If the actual field degree equals the binomial degree, the actual root
is primitive. This conclusion uses field dimensions, not an integral basis. -/
theorem adjoin_uniformizer_binomial_root_eq_top
    {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]
    {c : R} (hc : Irreducible c) (e : ℕ) (he : 0 < e)
    (hdegree : Module.finrank F E = e) (θ : E)
    (hθ : θ ^ e = algebraMap F E (algebraMap R F c)) :
    IntermediateField.adjoin F {θ} = ⊤ := by
  apply (Field.primitive_element_iff_minpoly_natDegree_eq F θ).mpr
  rw [minpoly_eq_uniformizer_binomial F hc e he θ hθ, natDegree_X_pow_sub_C, hdegree]

/-- The determinant norm has the exact sign `(-1)^(e-1)`. No cancellation
of exponent-th powers is used. -/
theorem norm_uniformizer_binomial_root
    {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]
    {c : R} (hc : Irreducible c) (e : ℕ) (he : 0 < e)
    (hdegree : Module.finrank F E = e) (θ : E)
    (hθ : θ ^ e = algebraMap F E (algebraMap R F c)) :
    Algebra.norm F θ = (-1 : F) ^ (e - 1) * algebraMap R F c := by
  have hgen := adjoin_uniformizer_binomial_root_eq_top F hc e he hdegree θ hθ
  let pb := PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite F θ) hgen
  have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  have hmin := minpoly_eq_uniformizer_binomial F hc e he θ hθ
  simp only [pb, PowerBasis.ofAdjoinSimpleEqTop_gen,
    PowerBasis.ofAdjoinSimpleEqTop_dim, hmin, natDegree_X_pow_sub_C,
    coeff_sub, coeff_X_pow, coeff_C, (Nat.ne_of_gt he).symm,
    ite_false, ite_true, zero_sub] at hnorm
  rw [hnorm]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  simp [pow_succ]

end IsDiscreteValuationRing
