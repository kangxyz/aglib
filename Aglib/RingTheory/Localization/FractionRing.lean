/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Fraction rings after domain localization

The fraction-ring structure is transported through the original localization
and coefficient tower. This is the reusable construction extracted from
`Aglib.RingTheory.Nagata.Localization`; no replacement fraction field is chosen.
-/

@[expose] public noncomputable section

universe u

/-- A fraction ring of a domain localization is a fraction ring of the original
domain, with the same coefficient maps and scalar tower. -/
theorem IsFractionRing.of_domain_localization
    {R S K : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [CommRing K] [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] (M : Submonoid R) [IsLocalization M S]
    [IsFractionRing S K] : IsFractionRing R K := by
  have hM : M ≤ nonZeroDivisors R := by
    intro x hx
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    exact (IsLocalization.map_units S ⟨x, hx⟩).ne_zero (by simp [hzero])
  have hinj := IsLocalization.injective S hM
  have hsub : (nonZeroDivisors S).comap (algebraMap R S) = nonZeroDivisors R :=
    le_antisymm (comap_nonZeroDivisors_le_of_injective hinj)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  change IsLocalization (nonZeroDivisors R) K
  rw [← hsub]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors S) K (fun _ hx => hx.mem_nonZeroDivisors)

