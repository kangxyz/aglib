/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.QuotientEndomorphismComparison
public import Aglib.RingTheory.Reflexive.DualPi
public import Aglib.RingTheory.QuotSMulTop.Pi
public import Aglib.RingTheory.QuotSMulTop.LocalizedFree

/-! Descent of an actual endomorphism-product relation to the bidual of a scalar quotient. -/

@[expose] public section

noncomputable section

universe u

namespace QuotSMulTop

variable {R : Type u} [CommRing R] (a : R) (M : Type u) [AddCommGroup M] [Module R M]
  {r : ℕ}

local notation "Q" => R ⧸ Ideal.span (Singleton.singleton a : Set R)
local notation "U" => QuotSMulTop a M
local notation "Nq" => Module.Dual Q (Module.Dual Q U)
local notation "D" => QuotSMulTop a (Module.End R M)

/-- The original endomorphism-product equivalence descends to the actual scalar quotients. -/
def quotientEndomorphismPiSourceEquiv (e : Module.End R M ≃ₗ[R] (Fin r → M)) :
    D ≃ₗ[Q] (Fin r → U) :=
  ((QuotSMulTop.congr a e).extendScalarsOfSurjective Ideal.Quotient.mk_surjective).trans
    (piEquiv a M (Fin r))

@[simp]
theorem quotientEndomorphismPiSourceEquiv_mk
    (e : Module.End R M ≃ₗ[R] (Fin r → M)) (f : Module.End R M) :
    quotientEndomorphismPiSourceEquiv a M e (Submodule.Quotient.mk f) =
      fun i ↦ Submodule.Quotient.mk (e f i) := rfl

/-- An actual endomorphism-product relation passes to the bidual of a regular scalar
quotient, using punctured freeness rather than a global Hom base-change hypothesis. -/
def quotientBidualEndomorphismPiEquiv [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R M] [IsRegularLocalRing Q]
    (ha : IsSMulRegular M a)
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M))
    (e : Module.End R M ≃ₗ[R] (Fin r → M))
    (d : ℕ) (hd : ringKrullDim Q = (d : ℕ)) (h2 : 2 ≤ d) :
    Module.End Q Nq ≃ₗ[Q] (Fin r → Nq) := by
  let := Module.Finite.of_restrictScalars_finite R Q U
  have hp (p : PrimeSpectrum R) (h : p.asIdeal ≠ IsLocalRing.maximalIdeal R) :
      Module.Projective (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) := by
    let := hfree p h
    infer_instance
  have hq (q : PrimeSpectrum Q) (h : q.asIdeal ≠ IsLocalRing.maximalIdeal Q) :
      Module.IsReflexive (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl U) := by
    let := free_punctured_of_free_punctured a M hfree q h
    infer_instance
  let h := quotientEndomorphismBidualEquiv a M ha hp hq d hd h2
  let q := quotientEndomorphismPiSourceEquiv a M e
  exact h.symm.trans (q.dualMap.dualMap.trans (Module.Dual.piDoubleDualEquiv Q U (Fin r)))

end QuotSMulTop
