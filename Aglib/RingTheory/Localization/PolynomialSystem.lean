/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.Integer

/-!
# Common denominators for polynomial systems

A finite family of polynomials over a localization admits a common denominator
from the original localization monoid. Multiplication by this denominator
preserves its zero set in every target receiving the original localization
map, because that actual denominator is a unit there.
-/

@[expose] public section

noncomputable section

open MvPolynomial

universe u v w₁ w₂ t

namespace IsLocalization

/-- Clear the coefficients of a finite polynomial family using a single
actual localization denominator, preserving zero sets under every target map. -/
theorem exists_common_denominator_polynomial_system
    {R : Type u} {L : Type v} {σ : Type w₁} {ι : Type w₂}
    [CommRing R] [CommRing L] [Algebra R L]
    (M : Submonoid R) [IsLocalization M L] [Finite ι]
    (F : ι → MvPolynomial σ L) :
    ∃ (s : M) (G : ι → MvPolynomial σ R),
      (∀ i, MvPolynomial.map (algebraMap R L) (G i) = C (algebraMap R L s) * F i) ∧
      ∀ (T : Type t) [CommRing T] (φ : L →+* T) (y : σ → T) (i : ι),
        eval₂ (φ.comp (algebraMap R L)) y (G i) = 0 ↔ eval₂ φ y (F i) = 0 := by
  classical
  let := Fintype.ofFinite ι
  let c : Finset L := Finset.univ.biUnion fun i => (F i).coeffs
  obtain ⟨s, hs⟩ := exist_integer_multiples_of_finset M c
  have hF (i : ι) : C (algebraMap R L s) * F i ∈
      Set.range (MvPolynomial.map (algebraMap R L)) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro a ha
    obtain ⟨m, _, rfl⟩ := mem_coeffs_iff.mp ha
    rw [coeff_C_mul]
    by_cases hz : (F i).coeff m = 0
    · exact ⟨0, by simp [hz]⟩
    · have hm : (F i).coeff m ∈ c :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, coeff_mem_coeffs m hz⟩
      obtain ⟨b, hb⟩ := hs ((F i).coeff m) hm
      exact ⟨b, by simpa only [Algebra.smul_def] using hb⟩
  choose G hG using hF
  refine ⟨s, G, hG, ?_⟩
  intro T _ φ y i
  rw [← eval₂_map, hG i, eval₂_mul, eval₂_C]
  exact ((IsLocalization.map_units L s).map φ).mul_right_eq_zero

end IsLocalization
