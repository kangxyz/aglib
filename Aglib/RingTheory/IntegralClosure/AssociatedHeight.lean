/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.AssociatedPrincipal
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! Associated primes of nonzero principal quotients of normal Noetherian domains. -/

@[expose] public section

noncomputable section

open Module.associatedPrimes

namespace IsAssociatedPrime

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- Associated primes of a nonzero principal quotient in a normal Noetherian domain have
height at most one. -/
theorem height_le_one_of_principal {p : Ideal R} {b : R} (hb : b ≠ 0)
    (h : IsAssociatedPrime p (R ⧸ Ideal.span {b})) : p.height ≤ 1 := by
  let := h.isPrime
  let Rₚ := Localization.AtPrime p
  let := isIntegrallyClosed_of_isLocalization Rₚ p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  let f := Algebra.linearMap R Rₚ
  let J : Submodule R R := Ideal.span {b}
  have hJ : J.localized' Rₚ p.primeCompl f = Ideal.span {algebraMap R Rₚ b} := by
    change (Submodule.span R {b}).localized' Rₚ p.primeCompl f = _
    rw [Submodule.localized'_span]
    simp only [Set.image_singleton]
    rfl
  have hloc : IsAssociatedPrime (IsLocalRing.maximalIdeal Rₚ)
      (Rₚ ⧸ J.localized' Rₚ p.primeCompl f) := by
    apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      p.primeCompl (J.toLocalizedQuotient' Rₚ p.primeCompl f)
    change IsAssociatedPrime ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).under R)
      (R ⧸ Ideal.span {b})
    rwa [Localization.AtPrime.under_maximalIdeal]
  rw [hJ] at hloc
  have hb' : algebraMap R Rₚ b ≠ 0 := by
    simpa only [map_zero] using (IsLocalization.injective Rₚ p.primeCompl_le_nonZeroDivisors).ne hb
  have hh := IsLocalRing.maximalIdeal_height_le_one_of_associated_principal hb' hloc
  have he := IsLocalization.height_under p.primeCompl (IsLocalRing.maximalIdeal Rₚ)
  rw [Localization.AtPrime.under_maximalIdeal] at he
  exact he ▸ hh

end IsAssociatedPrime
