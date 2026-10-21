/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.BidualEndomorphismComparison
public import Aglib.RingTheory.Reflexive.QuotientEndomorphismFiniteDefect
public import Aglib.RingTheory.Reflexive.Hom
public import Aglib.RingTheory.RegularLocalRing.Domain
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthDualComparison

/-! The actual quotient-endomorphism action determines endomorphisms of the quotient bidual. -/

@[expose] public section

noncomputable section

universe u

namespace QuotSMulTop

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (a : R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "Q" => R ⧸ Ideal.span (Singleton.singleton a : Set R)
local notation "U" => QuotSMulTop a M
local notation "Nq" => Module.Dual Q (Module.Dual Q U)
local notation "D" => QuotSMulTop a (Module.End R M)

/-- Finite-length defects identify the actual double dual of the quotient action. -/
theorem quotientEndomorphism_doubleDual_bijective [IsRegularLocalRing Q]
    (ha : IsSMulRegular M a)
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Projective (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M))
    (d : ℕ) (hd : ringKrullDim Q = (d : ℕ)) (h2 : 2 ≤ d) :
    Function.Bijective (quotientEndomorphism a M).dualMap.dualMap := by
  let f := quotientEndomorphism a M
  have hker : IsFiniteLength Q f.ker := by
    rw [LinearMap.ker_eq_bot.mpr (quotientEndomorphism_injective a M ha)]
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact IsRegularLocalRing.bijective_doubleDualMap_of_isFiniteLength Q
    (M := D) (N := Module.End Q U) f hker
    (isFiniteLength_coker_quotientEndomorphism a M hfree) d hd h2

/-- The original quotient-endomorphism map, followed by double transposition, becomes
an isomorphism from the bidual of its source to endomorphisms of the quotient bidual.
Regularity of the quotient ring is an explicit input. -/
def quotientEndomorphismBidualEquiv [IsRegularLocalRing Q]
    (ha : IsSMulRegular M a)
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Projective (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M))
    (hlocal : ∀ p : PrimeSpectrum Q, p.asIdeal ≠ IsLocalRing.maximalIdeal Q →
      Module.IsReflexive (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl U))
    (d : ℕ) (hd : ringKrullDim Q = (d : ℕ)) (h2 : 2 ≤ d) :
    Module.Dual Q (Module.Dual Q D) ≃ₗ[Q] Module.End Q Nq := by
  let := Module.Finite.of_restrictScalars_finite R Q U
  let := IsRegularLocalRing.isDomain_of_regularLocal Q
  let := Module.IsReflexive.dual_of_finite (R := Q) (M := Module.Dual Q U)
  let := Module.IsReflexive.linearMap (R := Q) (M := Nq) (N := Nq)
  let f := quotientEndomorphism a M
  let ef := LinearEquiv.ofBijective f.dualMap.dualMap
    (quotientEndomorphism_doubleDual_bijective a M ha hfree d hd h2)
  let eg := (Module.Dual.doubleTransposeDualEquiv Q U hlocal d hd h2).dualMap
  exact (ef.trans eg).trans (Module.evalEquiv Q (Module.End Q Nq)).symm

/-- The comparison retains the original action, rather than merely identifying the
abstract modules. -/
theorem quotientEndomorphismBidualEquiv_eval [IsRegularLocalRing Q]
    (ha : IsSMulRegular M a)
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Projective (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M))
    (hlocal : ∀ p : PrimeSpectrum Q, p.asIdeal ≠ IsLocalRing.maximalIdeal Q →
      Module.IsReflexive (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl U))
    (d : ℕ) (hd : ringKrullDim Q = (d : ℕ)) (h2 : 2 ≤ d) (x : D) :
    quotientEndomorphismBidualEquiv a M ha hfree hlocal d hd h2 (Module.Dual.eval Q D x) =
      Module.Dual.doubleTranspose Q U (quotientEndomorphism a M x) := by
  let := Module.Finite.of_restrictScalars_finite R Q U
  let := IsRegularLocalRing.isDomain_of_regularLocal Q
  let := Module.IsReflexive.dual_of_finite (R := Q) (M := Module.Dual Q U)
  let := Module.IsReflexive.linearMap (R := Q) (M := Nq) (N := Nq)
  change (Module.evalEquiv Q (Module.End Q Nq)).symm
    (Module.Dual.eval Q (Module.End Q Nq)
      (Module.Dual.doubleTranspose Q U (quotientEndomorphism a M x))) = _
  exact (Module.evalEquiv Q (Module.End Q Nq)).symm_apply_apply _

end QuotSMulTop
