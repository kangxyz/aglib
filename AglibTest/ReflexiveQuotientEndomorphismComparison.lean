/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.QuotientEndomorphismPi

/-! The quotient-bidual endomorphism relation without global Hom base change. -/

@[expose] public section

noncomputable section

universe u

example {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (a : R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsRegularLocalRing (R ⧸ Ideal.span {a})]
    (ha : IsSMulRegular M a)
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M))
    {r : ℕ} (e : Module.End R M ≃ₗ[R] (Fin r → M))
    (d : ℕ) (hd : ringKrullDim (R ⧸ Ideal.span {a}) = (d : ℕ)) (h2 : 2 ≤ d) :
    Module.End (R ⧸ Ideal.span {a})
        (Module.Dual (R ⧸ Ideal.span {a})
          (Module.Dual (R ⧸ Ideal.span {a}) (QuotSMulTop a M))) ≃ₗ[R ⧸ Ideal.span {a}]
      (Fin r → Module.Dual (R ⧸ Ideal.span {a})
        (Module.Dual (R ⧸ Ideal.span {a}) (QuotSMulTop a M))) :=
  QuotSMulTop.quotientBidualEndomorphismPiEquiv a M ha hfree e d hd h2

example {R : Type u} [CommRing R] (a : R) (M : Type u)
    [AddCommGroup M] [Module R M] {r : ℕ}
    (e : Module.End R M ≃ₗ[R] (Fin r → M)) (f : Module.End R M) :
    QuotSMulTop.quotientEndomorphismPiSourceEquiv a M e (Submodule.Quotient.mk f) =
      fun i ↦ Submodule.Quotient.mk (e f i) :=
  QuotSMulTop.quotientEndomorphismPiSourceEquiv_mk a M e f
