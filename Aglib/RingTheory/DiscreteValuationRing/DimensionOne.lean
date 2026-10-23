/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.AssociatedHeight
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Deriving the actual DVR inputs of the associated-prime completion criterion

The local normal and regular criteria are proved at abstract ring carriers,
then applied to the original native prime localization. Associated primes
of nonzero principal quotients supply the DVR inputs used in the
associated-prime completion criterion.
-/

@[expose] public noncomputable section

open IsLocalRing

/-- A normal Noetherian local domain of dimension at most one is a DVR
when it is not a field. -/
theorem IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A]
    (hdim : ringKrullDim A ≤ 1) (hnf : ¬ IsField A) : IsDiscreteValuationRing A := by
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim
  let : Ring.DimensionLEOne A :=
    ⟨fun {P} hP hp =>
      (Ring.krullDimLE_one_iff_of_isPrime_bot (R := A)).mp inferInstance P hP hp⟩
  let : IsDedekindDomain A :=
    (isDedekindDomain_iff A (FractionRing A)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance⟩
  exact ((IsDiscreteValuationRing.TFAE A hnf).out 1 3).mpr
    (inferInstance : IsDedekindDomain A)

/-- A regular local domain of dimension one is a DVR, using the native
cotangent-space criterion. -/
theorem IsDiscreteValuationRing.of_isRegularLocalRing_of_dim_eq_one
    (A : Type*) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  apply (IsLocalRing.finrank_CotangentSpace_eq_one_iff (R := A)).mp
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
  rw [hdim] at hcot
  exact_mod_cast hcot

/-- An associated prime of the original principal quotient contains its
original equation. No normality or Noetherianity is needed for this fact. -/
theorem IsAssociatedPrime.mem_of_quotient_span_singleton
    {R : Type*} [CommRing R] {p : Ideal R} {x : R}
    (h : IsAssociatedPrime p (R ⧸ Ideal.span {x})) : x ∈ p := by
  obtain ⟨y, hy⟩ := h.2
  rw [hy]
  apply Ideal.le_radical
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def]
  change Ideal.Quotient.mk (Ideal.span {x}) x * y = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x), zero_mul]

/-- The ambient localization at an associated prime of a nonzero
principal quotient of a normal Noetherian domain is a DVR. -/
theorem IsAssociatedPrime.isDiscreteValuationRing_atPrime_of_principal
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {p : Ideal R} [p.IsPrime] {x : R}
    (hx : x ≠ 0) (hp : IsAssociatedPrime p (R ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hxp : x ∈ p := hp.mem_of_quotient_span_singleton
  have hpne : p ≠ ⊥ := by
    intro he
    exact hx (by simpa only [he, Ideal.mem_bot] using hxp)
  have hheight : p.height = 1 :=
    le_antisymm (hp.height_le_one_of_principal hx)
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpne))
  let A := Localization.AtPrime p
  let : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  let : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A, hheight]
    rfl
  exact IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one A hdim.le
    (IsLocalization.AtPrime.not_isField R hpne A)

/-- The classical regular-ambient branch: a prime minimal over a nonzero
principal ideal has DVR localization when that ambient localization is regular. -/
theorem IsRegularLocalRing.isDiscreteValuationRing_atPrime_of_minimal_principal
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {p : Ideal R} [p.IsPrime] {x : R} (hx : x ≠ 0)
    (hp : p ∈ (Ideal.span {x}).minimalPrimes)
    [IsRegularLocalRing (Localization.AtPrime p)] :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hxp : x ∈ p := hp.1.2 (Ideal.mem_span_singleton_self x)
  have hpne : p ≠ ⊥ := by
    intro he
    exact hx (by simpa only [he, Ideal.mem_bot] using hxp)
  have hheight : p.height = 1 :=
    le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hp)
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpne))
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hheight]
    rfl
  exact IsDiscreteValuationRing.of_isRegularLocalRing_of_dim_eq_one
    (Localization.AtPrime p) hdim
