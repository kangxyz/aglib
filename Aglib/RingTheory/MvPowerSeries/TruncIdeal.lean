/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.AdicComplete

/-! # Truncation errors in actual variable ideals -/

@[expose] public section

namespace MvPowerSeries

universe u v w
variable {σ : Type u} {R : Type v} [Finite σ] [CommRing R]

/-- The tail of total-degree truncation lies in the corresponding power of
 the variable ideal, not merely in a coefficientwise vanishing predicate. -/
theorem sub_truncTotal_mem_span_X_pow (n : ℕ) (f : MvPowerSeries σ R) :
    f - (f.truncTotal n : MvPowerSeries σ R) ∈
      (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ^ n := by
  have hmap : (MvPolynomial.idealOfVars σ R).map
      (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext i
    simp [algebraMap_apply']
  simpa only [Ideal.map_pow, hmap] using sub_truncTotal_mem_map_idealOfVars_pow n f

/-- Total-degree truncation below degree one is the constant coefficient. -/
theorem truncTotal_one_eq_C_constantCoeff (f : MvPowerSeries σ R) :
    f.truncTotal 1 = MvPolynomial.C (constantCoeff f) := by
  ext d
  by_cases hd : d = 0
  · subst d
    simp [coeff_truncTotal_eq_ite, coeff_zero_eq_constantCoeff_apply]
  · rw [MvPolynomial.coeff_C_of_ne_zero hd]
    simp [coeff_truncTotal_eq_ite, Finsupp.degree_eq_zero_iff, hd]

variable [IsLocalRing R]

/-- To control the image of the mixed maximal ideal, it suffices to control
coefficient nonunits and variables. -/
theorem maximalIdeal_le_comap_of_C_X {S : Type w} [CommRing S]
    (E : MvPowerSeries σ R →+* S) (J : Ideal S)
    (hC : ∀ r ∈ IsLocalRing.maximalIdeal R, E (C r) ∈ J)
    (hX : ∀ i, E (X i) ∈ J) :
    IsLocalRing.maximalIdeal (MvPowerSeries σ R) ≤ J.comap E := by
  intro f hf
  have hc : constantCoeff f ∈ IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_constantCoeff] using hf
  have hv : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ J.comap E := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hX i
  have ht := sub_truncTotal_mem_span_X_pow 1 f
  rw [pow_one, truncTotal_one_eq_C_constantCoeff, MvPolynomial.coe_C] at ht
  have he := J.add_mem (hv ht) (hC _ hc)
  change E f ∈ J
  simpa only [map_sub, sub_add_cancel] using he

end MvPowerSeries
