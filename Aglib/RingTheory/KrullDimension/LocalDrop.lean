/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Height

/-!
# Strict dimension drop at a nonmaximal prime of a finite-dimensional local ring

A prime chain ending at a nonmaximal prime extends by the maximal ideal.
The height bound supplies the natural-number dimension required for induction.
No Noetherianity, regularity or catenarity hypothesis is needed.
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A nonmaximal localization of a finite-dimensional local ring has a strictly
smaller natural-number Krull dimension. -/
theorem exists_ringKrullDim_localization_lt (d : ℕ)
    (hd : ringKrullDim R = (d : ℕ)) (p : PrimeSpectrum R)
    (hp : p.asIdeal ≠ maximalIdeal R) :
    ∃ n : ℕ, n < d ∧ ringKrullDim (Localization.AtPrime p.asIdeal) = (n : ℕ) := by
  have hm : (maximalIdeal R).height = (d : ℕ∞) :=
    WithBot.coe_injective (maximalIdeal_height_eq_ringKrullDim.trans hd)
  have hlt : p.asIdeal < maximalIdeal R :=
    lt_of_le_of_ne (le_maximalIdeal p.isPrime.ne_top) hp
  have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hm] at hh
  have hfinite : p.asIdeal.height ≠ ⊤ := by
    intro h
    simp [h] at hh
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  refine ⟨n, ?_, ?_⟩
  · rw [← hn] at hh
    have : n + 1 ≤ d := by exact_mod_cast hh
    omega
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, ← hn]
    rfl

/-- The numerical strict dimension inequality at a nonmaximal prime. -/
theorem ringKrullDim_localization_lt (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ maximalIdeal R) :
    ringKrullDim (Localization.AtPrime p.asIdeal) < (d : ℕ) := by
  obtain ⟨n, hn, he⟩ := exists_ringKrullDim_localization_lt d hd p hp
  rw [he]
  exact_mod_cast hn

end IsLocalRing
