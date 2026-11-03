/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Finite
public import Aglib.RingTheory.Nagata.Localization
public import Aglib.RingTheory.AdicCompletion.AssociatedPrimeCriterion
public import Aglib.RingTheory.AdicCompletion.FiniteReducedDescent
public import Aglib.RingTheory.DiscreteValuationRing.DimensionOne
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Reduced completion of a Nagata local domain

The dimension induction uses the actual finite normalization, its maximal localizations,
and associated prime quotients of a nonzero principal ideal. Every induction call has a
strictly smaller natural dimension bound. This does not use finite-type Nagata ascent or
finite normalization of arbitrary complete local rings.

Reference: Stacks Project, Lemma 10.162.13.
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

/-- A genuine natural-number dimension induction proves reducedness of the original
maximal-adic completion. The finite bound is arbitrary, not restricted to surfaces. -/
theorem IsNagataRing.isReduced_completion_of_dimLE (d : ℕ)
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ (d : ℕ)) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  induction d generalizing R with
  | zero =>
    let : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hdim
    let : Field R := (Ring.KrullDimLE.isField_of_isDomain (R := R)).toField
    exact fieldCompletionReduced R
  | succ d ih =>
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
    have hdimC : ringKrullDim C ≤ (d + 1 : ℕ) :=
      (integral_dimension_le R C).trans hdim
    apply AdicCompletion.isReduced_of_finite_of_completed_localizations R C hinj
    intro q hq
    let T := Localization.AtPrime q
    have hT : IsNagataRing.{u, 0} T := hC.of_isLocalization q.primeCompl
    let : IsNoetherianRing T := hT.isNoetherianRing
    let : IsIntegrallyClosed T :=
      isIntegrallyClosed_of_isLocalization T q.primeCompl q.primeCompl_le_nonZeroDivisors
    have hdimT : ringKrullDim T ≤ (d + 1 : ℕ) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q T]
      exact (Ideal.height_le_ringKrullDim_of_ne_top (I := q) hq.ne_top).trans hdimC
    by_cases hf : IsField T
    · let : Field T := hf.toField
      exact fieldCompletionReduced T
    · have hm : maximalIdeal T ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal T) hf
      obtain ⟨x, hxm, hx⟩ := (maximalIdeal T).ne_bot_iff.mp hm
      apply AdicCompletion.isReduced_of_associated_dvr_quotients T x hxm hx
      · intro p hp hass
        exact hass.isDiscreteValuationRing_atPrime_of_principal hx
      · intro p hp hass
        let : IsLocalRing (T ⧸ p) :=
          IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
        have hxp : x ∈ p := hass.mem_of_quotient_span_singleton
        have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p)
          Ideal.Quotient.mk_surjective (r := x)
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
          (Ideal.Quotient.eq_zero_iff_mem.mpr hxp)
        have hdimQ : ringKrullDim (T ⧸ p) ≤ (d : ℕ) := by
          apply ENat.WithBot.add_le_add_one_right_iff.mp
          simpa only [Nat.cast_add, Nat.cast_one] using hdrop.trans hdimT
        exact ih (hT.quotient p) hdimQ

/-- Every Nagata local domain is analytically unramified, with no dimension hypothesis. -/
theorem IsNagataRing.isReduced_completion
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsNagataRing.{u, 0} R) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing R := h.isNoetherianRing
  apply h.isReduced_completion_of_dimLE (maximalIdeal R).spanFinrank
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast (maximalIdeal R).height_le_spanFinrank (maximalIdeal.isMaximal R).ne_top
