/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialCompletionQuotient
public import Aglib.RingTheory.AdicCompletion.NoetherianRing
public import Aglib.RingTheory.AdicCompletion.Transition
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-! # Completion of the actual polynomial local ring -/

@[expose] public section
noncomputable section
open IsLocalRing

namespace PolynomialLocalRing

universe u
variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)

local notation "Ahat" => AdicCompletion (maximalIdeal R) R
local notation "B" => MvPowerSeries (Fin n) Ahat
local notation "L" => PolynomialLocalRing R n
local notation "F" => (MvPolynomial.aeval (fun i : Fin n => (MvPowerSeries.X i : B)))

/-- Completeness of the target for its own mixed maximal ideal. -/
theorem formalSeries_isAdicComplete : IsAdicComplete (maximalIdeal B) B := by
  have : IsNoetherianRing Ahat := AdicCompletion.isNoetherianRing R (maximalIdeal R)
  exact MvPowerSeries.isAdicComplete_maximalIdeal (Fin n) Ahat

attribute [local instance] formalSeries_isAdicComplete

/-- Actual local finite quotients are identified with the actual formal finite quotients. -/
def localMixedQuotientEquiv (k : ℕ) :
    (L ⧸ maximalIdeal L ^ k) ≃ₐ[R] B ⧸ maximalIdeal B ^ k :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdealPow
    (originIdeal R n) L k).symm.restrictScalars R).trans
    (mixedQuotientAlgEquiv R n k)

@[simp] theorem localMixedQuotientEquiv_mk_polynomial (k : ℕ) (f : MvPolynomial (Fin n) R) :
    localMixedQuotientEquiv R n k
        (algebraMap (MvPolynomial (Fin n) R) (L ⧸ maximalIdeal L ^ k) f) =
      Ideal.Quotient.mk _ (F f) := by
  rw [← Ideal.Quotient.mk_algebraMap]
  change mixedQuotientAlgEquiv R n k
    ((IsLocalization.AtPrime.equivQuotMaximalIdealPow (originIdeal R n) L k).symm
      (Ideal.Quotient.mk _ (algebraMap _ L f))) = _
  rw [← IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk (originIdeal R n) L k f,
    AlgEquiv.symm_apply_apply, mixedQuotientAlgEquiv_mk]

/-- Compatibility is checked on actual polynomial representatives, using the
native localization quotient equivalence, not chosen fraction representatives. -/
theorem localMixedQuotientEquiv_factorPow {i j : ℕ} (hij : i ≤ j)
    (x : L ⧸ maximalIdeal L ^ j) :
    Ideal.Quotient.factorPow (maximalIdeal B) hij (localMixedQuotientEquiv R n j x) =
      localMixedQuotientEquiv R n i (Ideal.Quotient.factorPow (maximalIdeal L) hij x) := by
  obtain ⟨q, rfl⟩ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (originIdeal R n) L j).surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
    Ideal.Quotient.mk_algebraMap, localMixedQuotientEquiv_mk_polynomial]
  change Ideal.Quotient.mk (maximalIdeal B ^ i) (F f) =
    localMixedQuotientEquiv R n i (Ideal.Quotient.mk _ (algebraMap _ L f))
  simpa only [Ideal.Quotient.mk_algebraMap] using
    (localMixedQuotientEquiv_mk_polynomial R n i f).symm

theorem localMixedQuotientEquiv_symm_factorPow {i j : ℕ} (hij : i ≤ j)
    (x : B ⧸ maximalIdeal B ^ j) :
    Ideal.Quotient.factorPow (maximalIdeal L) hij ((localMixedQuotientEquiv R n j).symm x) =
      (localMixedQuotientEquiv R n i).symm (Ideal.Quotient.factorPow (maximalIdeal B) hij x) := by
  apply (localMixedQuotientEquiv R n i).injective
  rw [AlgEquiv.apply_symm_apply, ← localMixedQuotientEquiv_factorPow,
    AlgEquiv.apply_symm_apply]

theorem completionToFormal_compatible {i j : ℕ} (hij : i ≤ j) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := maximalIdeal B) hij)).comp
      ((localMixedQuotientEquiv R n j).toAlgHom.comp
        ((AdicCompletion.evalₐ (maximalIdeal L) j).restrictScalars R)) =
      (localMixedQuotientEquiv R n i).toAlgHom.comp
        ((AdicCompletion.evalₐ (maximalIdeal L) i).restrictScalars R) := by
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.factorPow (maximalIdeal B) hij
    (localMixedQuotientEquiv R n j (AdicCompletion.evalₐ (maximalIdeal L) j x)) = _
  rw [localMixedQuotientEquiv_factorPow, AdicCompletion.factorPow_evalₐ]
  rfl

/-- The actual completion-to-formal-series map induced by the mixed quotient maps. -/
def completionToFormal : AdicCompletion (maximalIdeal L) L →ₐ[R] B :=
  IsAdicComplete.liftAlgHom (maximalIdeal B)
    (fun k => (localMixedQuotientEquiv R n k).toAlgHom.comp
      ((AdicCompletion.evalₐ (maximalIdeal L) k).restrictScalars R))
    (completionToFormal_compatible R n)

theorem formalToCompletion_compatible {i j : ℕ} (hij : i ≤ j) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := maximalIdeal L) hij)).comp
      ((localMixedQuotientEquiv R n j).symm.toAlgHom.comp
        (Ideal.Quotient.mkₐ R (maximalIdeal B ^ j))) =
      (localMixedQuotientEquiv R n i).symm.toAlgHom.comp
        (Ideal.Quotient.mkₐ R (maximalIdeal B ^ i)) := by
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.factorPow (maximalIdeal L) hij
    ((localMixedQuotientEquiv R n j).symm (Ideal.Quotient.mk _ x)) = _
  rw [localMixedQuotientEquiv_symm_factorPow]
  rfl

/-- The inverse map into the native completion. -/
def formalToCompletion : B →ₐ[R] AdicCompletion (maximalIdeal L) L :=
  AdicCompletion.liftAlgHom (maximalIdeal L)
    (fun k => (localMixedQuotientEquiv R n k).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ R (maximalIdeal B ^ k)))
    (formalToCompletion_compatible R n)

@[simp] theorem mk_completionToFormal (k : ℕ) (x : AdicCompletion (maximalIdeal L) L) :
    Ideal.Quotient.mk (maximalIdeal B ^ k) (completionToFormal R n x) =
      localMixedQuotientEquiv R n k (AdicCompletion.evalₐ (maximalIdeal L) k x) := by
  unfold completionToFormal
  exact IsAdicComplete.mk_liftAlgHom _ _ (completionToFormal_compatible R n) k x

@[simp] theorem eval_formalToCompletion (k : ℕ) (x : B) :
    AdicCompletion.evalₐ (maximalIdeal L) k (formalToCompletion R n x) =
      (localMixedQuotientEquiv R n k).symm (Ideal.Quotient.mk (maximalIdeal B ^ k) x) := by
  unfold formalToCompletion
  exact AdicCompletion.evalₐ_liftAlgHom _ _ (formalToCompletion_compatible R n) k x

theorem completionToFormal_comp_formalToCompletion :
    (completionToFormal R n).comp (formalToCompletion R n) = AlgHom.id R B := by
  apply IsAdicComplete.algHom_ext (maximalIdeal B)
  intro k
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.mk (maximalIdeal B ^ k)
    (completionToFormal R n (formalToCompletion R n x)) = Ideal.Quotient.mk _ x
  rw [mk_completionToFormal, eval_formalToCompletion, AlgEquiv.apply_symm_apply]

theorem formalToCompletion_comp_completionToFormal :
    (formalToCompletion R n).comp (completionToFormal R n) =
      AlgHom.id R (AdicCompletion (maximalIdeal L) L) := by
  apply AlgHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro k
  change AdicCompletion.evalₐ (maximalIdeal L) k
    (formalToCompletion R n (completionToFormal R n x)) = _
  rw [eval_formalToCompletion, mk_completionToFormal, AlgEquiv.symm_apply_apply]
  rfl

/-- Completion of the actual polynomial localization is the actual formal
power-series ring over coefficient completion, through the original maps. -/
def completionEquiv : AdicCompletion (maximalIdeal L) L ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (completionToFormal R n) (formalToCompletion R n)
    (completionToFormal_comp_formalToCompletion R n)
    (formalToCompletion_comp_completionToFormal R n)

/-- The comparison preserves the original polynomial map, hence both its
coefficients and variables, exactly. -/
theorem completionEquiv_polynomial (f : MvPolynomial (Fin n) R) :
    completionEquiv R n (algebraMap L (AdicCompletion (maximalIdeal L) L)
      (algebraMap (MvPolynomial (Fin n) R) L f)) = F f := by
  have h : (fun f : MvPolynomial (Fin n) R =>
      completionEquiv R n (algebraMap L (AdicCompletion (maximalIdeal L) L)
        (algebraMap (MvPolynomial (Fin n) R) L f))) = F := by
    apply IsHausdorff.funext' (maximalIdeal B)
    intro k g
    change Ideal.Quotient.mk (maximalIdeal B ^ k)
      (completionToFormal R n (algebraMap L _ (algebraMap _ L g))) = _
    rw [mk_completionToFormal, (AdicCompletion.evalₐ (maximalIdeal L) k).commutes]
    change localMixedQuotientEquiv R n k
      (Ideal.Quotient.mk _ (algebraMap _ L g)) = _
    simpa only [Ideal.Quotient.mk_algebraMap] using
      localMixedQuotientEquiv_mk_polynomial R n k g
  exact congrFun h f

end PolynomialLocalRing
