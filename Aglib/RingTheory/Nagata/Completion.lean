/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Finite
public import Aglib.RingTheory.Nagata.Localization
public import Aglib.RingTheory.AdicCompletion.AssociatedPrimeCriterion
public import Aglib.RingTheory.AdicCompletion.FiniteReducedDescent
public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.RingTheory.DiscreteValuationRing.DimensionOne
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Reduced completions of Nagata local domains in dimensions at most two

The finite normalization comes from the actual Japanese condition.
Abstract normal-model producers retain
the original finite map before specializing to the literal normalization.
No F2/CN2 or arbitrary finite-type Nagata stability theorem is used.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

private theorem integral_dimension_le
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] : ringKrullDim C ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R C))
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under (R := R) hpq

private theorem fieldCompletionReduced (K : Type u) [Field K] :
    IsReduced (AdicCompletion (maximalIdeal K) K) := by
  rw [IsLocalRing.maximalIdeal_eq_bot]
  let e : AdicCompletion (⊥ : Ideal K) K ≃ₐ[K] K :=
    (AdicCompletion.ofAlgEquiv (S := K) (⊥ : Ideal K)).symm
  exact isReduced_of_injective e e.injective

private theorem normalCompletionReducedOne
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A] (hdim : ringKrullDim A ≤ 1) :
    IsReduced (AdicCompletion (maximalIdeal A) A) := by
  by_cases hf : IsField A
  · let : Field A := hf.toField
    exact fieldCompletionReduced A
  · let : IsDiscreteValuationRing A :=
      IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one A hdim hf
    infer_instance

private theorem finiteNormalModelReducedOne
    (R C : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra R C] [Module.Finite R C]
    (hinj : Function.Injective (algebraMap R C)) (hdim : ringKrullDim C ≤ 1) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  apply AdicCompletion.isReduced_of_finite_of_completed_localizations R C hinj
  intro q hq
  let T := Localization.AtPrime q
  let : IsNoetherianRing T := IsLocalization.isNoetherianRing q.primeCompl T inferInstance
  let : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hdimT : ringKrullDim T ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q T]
    exact (Ideal.height_le_ringKrullDim_of_ne_top (I := q) hq.ne_top).trans hdim
  exact normalCompletionReducedOne T hdimT

/-- A Nagata local domain of dimension at most one has reduced actual
maximal-ideal completion, in the same ambient Japanese test universe. -/
theorem IsNagataRing.isReduced_completion_of_dimLE_one
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 1) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing R := h.isNoetherianRing
  let K := FractionRing R
  let C := integralClosure R K
  let : Module.Finite R C := h.isJapaneseRing.finite_integralClosure K
  let : IsIntegrallyClosed C :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) (L := K) K
  have hinj : Function.Injective (algebraMap R C) := by
    intro a b hab
    apply IsFractionRing.injective R K
    exact congrArg (fun c : C => (c : K)) hab
  let : Algebra.IsIntegral R C := inferInstance
  have hdimC : ringKrullDim C ≤ 1 := (integral_dimension_le R C).trans hdim
  exact finiteNormalModelReducedOne R C hinj hdimC

private theorem normalCompletionReducedTwo
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] [IsIntegrallyClosed R]
    (h : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  by_cases hf : IsField R
  · let : Field R := hf.toField
    exact fieldCompletionReduced R
  · have hm : maximalIdeal R ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal R) hf
    obtain ⟨x, hxm, hx⟩ := (maximalIdeal R).ne_bot_iff.mp hm
    apply AdicCompletion.isReduced_of_associated_dvr_quotients R x hxm hx
    · intro p hp hass
      exact hass.isDiscreteValuationRing_atPrime_of_principal hx
    · intro p hp hass
      let : IsLocalRing (R ⧸ p) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      have hxp : x ∈ p := hass.mem_of_quotient_span_singleton
      have hdimQ : ringKrullDim (R ⧸ p) ≤ 1 := by
        apply ENat.WithBot.add_le_add_one_right_iff.mp
        have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p)
          Ideal.Quotient.mk_surjective (r := x)
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
          (Ideal.Quotient.eq_zero_iff_mem.mpr hxp)
        convert hdrop.trans hdim using 1
        norm_num
      exact (h.quotient p).isReduced_completion_of_dimLE_one hdimQ

private theorem finiteNormalNagataModelReducedTwo
    (R C : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra R C] [Module.Finite R C]
    (hinj : Function.Injective (algebraMap R C))
    (hC : IsNagataRing.{u, 0} C) (hdim : ringKrullDim C ≤ 2) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing C := hC.isNoetherianRing
  apply AdicCompletion.isReduced_of_finite_of_completed_localizations R C hinj
  intro q hq
  let T := Localization.AtPrime q
  have hT : IsNagataRing.{u, 0} T := IsNagataRing.of_isLocalization q.primeCompl hC
  let : IsNoetherianRing T := hT.isNoetherianRing
  let : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hdimT : ringKrullDim T ≤ 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q T]
    exact (Ideal.height_le_ringKrullDim_of_ne_top (I := q) hq.ne_top).trans hdim
  exact normalCompletionReducedTwo T hT hdimT

/-- A Nagata local domain of dimension at most two has reduced actual
maximal-ideal completion, using finite normalization and the proved AC
criterion with its DVR and reduced-prime-completion inputs discharged. -/
theorem IsNagataRing.isReduced_completion_of_dimLE_two
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing R := h.isNoetherianRing
  let K := FractionRing R
  let C := integralClosure R K
  let : Module.Finite R C := h.isJapaneseRing.finite_integralClosure K
  let : IsIntegrallyClosed C :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) (L := K) K
  have hinj : Function.Injective (algebraMap R C) := by
    intro a b hab
    apply IsFractionRing.injective R K
    exact congrArg (fun c : C => (c : K)) hab
  let : Algebra.IsIntegral R C := inferInstance
  have hC : IsNagataRing.{u, 0} C := h.of_finite
  have hdimC : ringKrullDim C ≤ 2 := (integral_dimension_le R C).trans hdim
  exact finiteNormalNagataModelReducedTwo R C hinj hC hdimC
