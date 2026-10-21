/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.Localization.EndomorphismPi
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! Prime-localization consumer of the original finite-product endomorphism equivalence. -/

noncomputable section

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (r : ℕ)
    (e : Module.End R M ≃ₗ[R] (Fin r → M)) (p : Ideal R) [p.IsPrime] :
    Module.End (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ≃ₗ[
      Localization.AtPrime p] (Fin r → LocalizedModule p.primeCompl M) :=
  Module.End.localizedEquivPi p.primeCompl (Localization.AtPrime p)
    (LocalizedModule.mkLinearMap p.primeCompl M) e

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (r : ℕ)
    (e : Module.End R M ≃ₗ[R] (Fin r → M)) (p : Ideal R) [p.IsPrime]
    (f : Module.End R M) (i : Fin r) :
    Module.End.localizedEquivPi p.primeCompl (Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl M) e
      (IsLocalizedModule.mapExtendScalars p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl M)
        (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p) f) i =
      LocalizedModule.mkLinearMap p.primeCompl M (e f i) := by
  simp
