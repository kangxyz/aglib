/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.QuotSMulTop.LocalizedFree

/-! Scalar quotient stalks and the exact punctured-freeness interface. -/

example {R : Type*} [CommRing R] (a : R) (M : Type*) [AddCommGroup M] [Module R M]
    (q : PrimeSpectrum (R ⧸ Ideal.span {a}))
    [Module.Free (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule (q.asIdeal.under R).primeCompl M)] :
    Module.Free (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (QuotSMulTop a M)) :=
  QuotSMulTop.free_localizedModule_of_free_under a M q

example {R : Type*} [CommRing R] [IsLocalRing R] (a : R)
    [IsLocalRing (R ⧸ Ideal.span {a})] (M : Type*) [AddCommGroup M] [Module R M]
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    ∀ q : PrimeSpectrum (R ⧸ Ideal.span {a}),
      q.asIdeal ≠ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {a}) →
      Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (QuotSMulTop a M)) :=
  QuotSMulTop.free_punctured_of_free_punctured a M hfree

example {R : Type*} [CommRing R] [IsLocalRing R] (a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span {a}) := by
  let : Nontrivial (R ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr ha))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
