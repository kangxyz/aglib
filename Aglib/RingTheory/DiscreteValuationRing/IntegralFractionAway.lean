/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Fraction fields of algebraic extensions of a DVR

For an algebraic domain extension of a DVR, powers of any nonzero nonunit of the
base are cofinal among all nonzero denominators. Consequently its actual fraction
field is the localization obtained by inverting that base element. No local or
DVR hypothesis is imposed on the extension ring.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [Algebra R S]

/-- Nonzero denominators in an algebraic extension divide powers of a base nonunit. -/
theorem exists_dvd_map_pow_of_isAlgebraic [Algebra.IsAlgebraic R S]
    {c : R} (hc : c ≠ 0) (hcu : ¬ IsUnit c) {s : S} (hs : s ≠ 0) :
    ∃ n : ℕ, s ∣ algebraMap R S c ^ n := by
  obtain ⟨r, hr, hsr⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) s).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hs)
  obtain ⟨n, hn⟩ := exists_dvd_pow_of_nonzero_nonunit hc hcu hr
  exact ⟨n, hsr.trans (by simpa only [map_pow] using map_dvd (algebraMap R S) hn)⟩

/-- The actual fraction field of an algebraic domain extension is obtained by inverting
any nonzero nonunit of the base DVR. -/
theorem isLocalizationAway_of_isAlgebraic [Algebra.IsAlgebraic R S]
    (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E]
    (hinj : Function.Injective (algebraMap R S)) {c : R}
    (hc : c ≠ 0) (hcu : ¬ IsUnit c) :
    IsLocalization.Away (algebraMap R S c) E := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := E)
    (Submonoid.powers (algebraMap R S c)) (nonZeroDivisors S)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ((map_ne_zero_iff _ hinj).mpr hc)) ?_).mpr
      (inferInstance : IsLocalization (nonZeroDivisors S) E)
  intro s hs
  obtain ⟨n, hn⟩ := exists_dvd_map_pow_of_isAlgebraic hc hcu
    ((mem_nonZeroDivisors_iff_ne_zero).mp hs)
  exact ⟨algebraMap R S c ^ n, ⟨n, rfl⟩, hn⟩

/-- A finite torsion-free domain algebra has its fraction field by inverting a base uniformizer. -/
theorem isLocalizationAway_of_finite [Module.Finite R S] [Module.IsTorsionFree R S]
    (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E]
    {π : R} (hπ : Irreducible π) :
    IsLocalization.Away (algebraMap R S π) E :=
  isLocalizationAway_of_isAlgebraic E (FaithfulSMul.algebraMap_injective R S)
    hπ.ne_zero hπ.not_isUnit

/-- Clearing a denominator in the actual fraction field uses only a power of the
base uniformizer, compatibly with the specified algebra tower. -/
theorem exists_mul_pow_eq_algebraMap_of_finite
    [Module.Finite R S] [Module.IsTorsionFree R S]
    (E : Type*) [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
    [IsFractionRing S E] {π : R} (hπ : Irreducible π) (x : E) :
    ∃ (n : ℕ) (s : S), x * algebraMap R E π ^ n = algebraMap S E s := by
  let := isLocalizationAway_of_finite (S := S) E hπ
  simpa only [← IsScalarTower.algebraMap_apply R S E] using
    IsLocalization.Away.surj (algebraMap R S π) x

end IsDiscreteValuationRing
