/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.IntegralClosure.LocalizedGenericFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! Actual prime-localization fraction structure and the original generic normalization. -/

open scoped nonZeroDivisors TensorProduct

noncomputable section

example {A K E : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [CommRing E] [Algebra K E]
    [Algebra A E] [IsScalarTower A K E] [Algebra.IsIntegral K E]
    (p : Ideal A) [p.IsPrime] :
    letI := IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime p) K
      p.primeCompl A⁰ p.primeCompl_le_nonZeroDivisors
    Nonempty (K ⊗[Localization.AtPrime p]
      (Localization.AtPrime p ⊗[A] integralClosure A E) ≃ₐ[K] E) ∧
      IsFractionRing (Localization.AtPrime p) K := by
  let := IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime p) K
    p.primeCompl A⁰ p.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime p) K
    p.primeCompl A⁰ p.primeCompl_le_nonZeroDivisors
  let : IsFractionRing (Localization.AtPrime p) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl
      (Localization.AtPrime p) K
  exact ⟨⟨integralClosure.localizedGenericFiberEquiv A K E (Localization.AtPrime p)⟩,
    inferInstance⟩

example {A K E D : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [CommRing E] [Algebra K E]
    [Algebra A E] [IsScalarTower A K E] [Algebra.IsIntegral K E]
    [CommRing D] [Algebra A D] [Algebra D K] [IsScalarTower A D K]
    (b : integralClosure A E) :
    integralClosure.localizedGenericFiberEquiv A K E D (1 ⊗ₜ[D] (1 ⊗ₜ[A] b)) = b := by
  simp
