/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationEvaluation
public import Aglib.RingTheory.Henselian.PolynomialLocalCompletion
public import Aglib.RingTheory.Henselian.HenselizationCompletionCoherence
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Precision reflection for actual polynomial henselization evaluation

The original formal evaluation agrees with the actual completion comparison.
Its finite quotient coordinates are composites of the proved henselization and
mixed polynomial quotient equivalences. Consequently maximal-ideal precision is
reflected at every order. No Noetherianity of the henselization is assumed or used.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The actual completion comparison composed with the original henselization map. -/
def completionFormalMap (n : ℕ) :
    PolynomialLocalHenselization R n →ₐ[R] PolynomialLocalRing.FormalSeries R n :=
  (PolynomialLocalRing.completionEquiv R n).toAlgHom.comp
    ((Henselization.toAdicCompletion (PolynomialLocalRing R n)).restrictScalars R)

instance completionFormalMap_isLocalHom (n : ℕ) :
    IsLocalHom (completionFormalMap R n).toRingHom := by
  constructor
  intro x hx
  have h := hx.map (PolynomialLocalRing.completionEquiv R n).symm.toRingHom
  have h' : IsUnit (Henselization.toAdicCompletion (PolynomialLocalRing R n) x) := by
    change IsUnit ((PolynomialLocalRing.completionEquiv R n).symm
      (PolynomialLocalRing.completionEquiv R n
        (Henselization.toAdicCompletion (PolynomialLocalRing R n) x))) at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  exact IsLocalHom.map_nonunit
    (f := (Henselization.toAdicCompletion (PolynomialLocalRing R n)).toRingHom) x h'

/-- The completion-defined evaluation has the original localization restriction. -/
theorem completionFormalMap_comp_of (n : ℕ) :
    (completionFormalMap R n).comp
      (IsScalarTower.toAlgHom R (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)) =
        PolynomialLocalRing.toFormalSeries R n := by
  apply IsLocalization.algHom_ext (PolynomialLocalRing.originIdeal R n).primeCompl
  apply AlgHom.ext
  intro p
  change PolynomialLocalRing.completionEquiv R n
    (Henselization.toAdicCompletion (PolynomialLocalRing R n)
      (algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)
        (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) p))) =
    PolynomialLocalRing.toFormalSeries R n
      (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) p)
  rw [(Henselization.toAdicCompletion (PolynomialLocalRing R n)).commutes,
    PolynomialLocalRing.completionEquiv_polynomial,
    PolynomialLocalRing.toFormalSeries_algebraMap]
  rfl

/-- The original formal evaluation and the actual completion comparison coincide. -/
theorem completionFormalMap_eq_toFormalSeries (n : ℕ) :
    completionFormalMap R n = toFormalSeries R n :=
  (existsUnique_local_toFormalSeries R n).choose_spec.2 _
    ⟨completionFormalMap_isLocalHom R n, completionFormalMap_comp_of R n⟩

/-- The original formal map has the actual composite finite-quotient coordinates. -/
theorem mk_toFormalSeries (n c : ℕ) (x : PolynomialLocalHenselization R n) :
    Ideal.Quotient.mk (maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c)
      (toFormalSeries R n x) =
    PolynomialLocalRing.localMixedQuotientEquiv R n c
      ((Henselization.quotientMaximalIdealPowEquivAll (PolynomialLocalRing R n) c).symm
        (Ideal.Quotient.mk (maximalIdeal (PolynomialLocalHenselization R n) ^ c) x)) := by
  rw [← completionFormalMap_eq_toFormalSeries]
  change Ideal.Quotient.mk _ (PolynomialLocalRing.completionToFormal R n
    (Henselization.toAdicCompletion (PolynomialLocalRing R n) x)) = _
  rw [PolynomialLocalRing.mk_completionToFormal]
  have h := AlgHom.congr_fun
    (Henselization.completionMapInv_comp_of (PolynomialLocalRing R n)) x
  change Henselization.completionMapInv (PolynomialLocalRing R n)
    (algebraMap (PolynomialLocalHenselization R n)
      (AdicCompletion (maximalIdeal (PolynomialLocalHenselization R n))
        (PolynomialLocalHenselization R n)) x) =
      Henselization.toAdicCompletion (PolynomialLocalRing R n) x at h
  rw [← h, Henselization.eval_completionMapInv, (AdicCompletion.evalₐ _ c).commutes]
  rfl

/-- The actual formal map is surjective modulo every maximal-ideal power. -/
theorem quotient_mk_comp_toFormalSeries_surjective (n c : ℕ) :
    Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c)).comp
        (toFormalSeries R n).toRingHom) := by
  intro z
  obtain ⟨y, rfl⟩ := (PolynomialLocalRing.localMixedQuotientEquiv R n c).surjective z
  obtain ⟨w, rfl⟩ :=
    (Henselization.quotientMaximalIdealPowEquivAll (PolynomialLocalRing R n) c).symm.surjective y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨x, ?_⟩
  change Ideal.Quotient.mk _ (toFormalSeries R n x) = _
  exact mk_toFormalSeries R n c x

/-- Formal evaluation reflects and preserves every maximal-ideal power, including order zero. -/
theorem toFormalSeries_mem_maximalIdeal_pow_iff (n c : ℕ)
    (x : PolynomialLocalHenselization R n) :
    toFormalSeries R n x ∈ maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c ↔
      x ∈ maximalIdeal (PolynomialLocalHenselization R n) ^ c := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem,
    mk_toFormalSeries]
  rw [map_eq_zero_iff _ (PolynomialLocalRing.localMixedQuotientEquiv R n c).injective,
    map_eq_zero_iff _
      (Henselization.quotientMaximalIdealPowEquivAll (PolynomialLocalRing R n) c).symm.injective]

/-- The iterated target used by finite equation systems reflects the same actual precision. -/
theorem iteratedFormalMap_mem_maximalIdeal_pow_iff (n c : ℕ)
    (x : PolynomialLocalHenselization R (n + 1)) :
    iteratedFormalMap R n x ∈
        maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c ↔
      x ∈ maximalIdeal (PolynomialLocalHenselization R (n + 1)) ^ c := by
  let e := (MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n).toRingEquiv
  have hm : (maximalIdeal (PolynomialLocalRing.FormalSeries R (n + 1)) ^ c).map e =
      maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  change e (toFormalSeries R (n + 1) x) ∈ _ ↔ _
  rw [← hm, Ideal.apply_mem_of_equiv_iff]
  exact toFormalSeries_mem_maximalIdeal_pow_iff R (n + 1) c x

end PolynomialLocalHenselization
