/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Punctured freeness of scalar quotients

Freeness at the contracted prime survives passage to the actual scalar quotient
`QuotSMulTop a M`. The proof compares its localization with base change of the
original localized module. No finite-generation, Noetherianity or regularity
assumption is needed.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace QuotSMulTop

variable {R : Type*} [CommRing R] (a : R)
  (M : Type*) [AddCommGroup M] [Module R M]

/-- A scalar quotient is free at a prime whenever the original module is free
at its contracted prime. Both sides use the actual localized modules. -/
theorem free_localizedModule_of_free_under
    (q : PrimeSpectrum (R ⧸ Ideal.span {a}))
    [Module.Free (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule (q.asIdeal.under R).primeCompl M)] :
    Module.Free (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (QuotSMulTop a M)) := by
  let Q := R ⧸ Ideal.span {a}
  let p : PrimeSpectrum R := ⟨q.asIdeal.under R, inferInstance⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  let eQ : QuotSMulTop a M ≃ₗ[Q] Q ⊗[R] M :=
    (equivQuotTensor a M).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let e : LocalizedModule q.asIdeal.primeCompl (QuotSMulTop a M) ≃ₗ[
      Localization.AtPrime q.asIdeal]
      Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime p.asIdeal]
        LocalizedModule p.asIdeal.primeCompl M :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _) eQ) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R Q _ _ M) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R _ _ _ M).symm ≪≫ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ M).symm)
  exact Module.Free.of_equiv e.symm

/-- Punctured freeness descends to a scalar quotient of a local ring. The quotient
local-ring instance is supplied independently, for example by a proper scalar ideal. -/
theorem free_punctured_of_free_punctured [IsLocalRing R]
    [IsLocalRing (R ⧸ Ideal.span {a})]
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    ∀ q : PrimeSpectrum (R ⧸ Ideal.span {a}),
      q.asIdeal ≠ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {a}) →
      Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (QuotSMulTop a M)) := by
  intro q hq
  have hp : q.asIdeal.under R ≠ IsLocalRing.maximalIdeal R := by
    intro heq
    have hmax : (q.asIdeal.under R).IsMaximal := by
      rw [heq]
      infer_instance
    exact hq (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_of_isIntegral_of_isMaximal_under q.asIdeal hmax))
  let := hfree ⟨q.asIdeal.under R, inferInstance⟩ hp
  exact free_localizedModule_of_free_under a M q

end QuotSMulTop
