/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.ArithmeticFiniteType
public import Aglib.RingTheory.Nagata.Localization
public import Aglib.RingTheory.MinimalPrimes.FiniteCover
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Actual normalizations of smaller closed-support components

Nagata is propagated through the original finite transformation, localization
and closed quotient. Each literal minimal-prime quotient then has a finite
normalization in its own fraction field. This is a finite, normal, Noetherian
domain over that component, and its spectrum covers the entire component.
The rank is the bound of the original closed quotient, not a new certificate.
Arithmetic finite-type origins produce the Nagata input internally.
-/

@[expose] public noncomputable section

universe u

/-- The actual closed branch stays Nagata through arbitrary localization.
In particular the localization need not itself be finite type. -/
theorem IsNagataRing.finite_localized_quotient
    {R S L : Type u} [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Module.Finite R S] [Algebra S L]
    (M : Submonoid S) [IsLocalization M L]
    (hR : IsNagataRing.{u, 0} R) (J : Ideal L) :
    IsNagataRing.{u, 0} (L ⧸ J) :=
  (IsNagataRing.of_isLocalization (S := L) M
    (IsNagataRing.of_finite (S := S) hR)).quotient J

namespace integralClosure

/-- Complete original normalization data over a Nagata domain. The original
normalization map has every prime of the domain in its image. -/
theorem normal_model_of_nagata
    (Q : Type u) [CommRing Q] [IsDomain Q] (hQ : IsNagataRing.{u, 0} Q) :
    Module.Finite Q (integralClosure Q (FractionRing Q)) ∧
    IsNoetherianRing (integralClosure Q (FractionRing Q)) ∧
    IsIntegrallyClosed (integralClosure Q (FractionRing Q)) ∧
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap Q (integralClosure Q (FractionRing Q)))) ∧
    ringKrullDim (integralClosure Q (FractionRing Q)) ≤ ringKrullDim Q := by
  let : IsNoetherianRing Q := hQ.isNoetherianRing
  let : Module.Finite Q (integralClosure Q (FractionRing Q)) :=
    hQ.isJapaneseRing.finite_integralClosure (FractionRing Q)
  have hnormal : IsIntegrallyClosed (integralClosure Q (FractionRing Q)) :=
    isIntegrallyClosedOfFiniteExtension (FractionRing Q)
  let : FaithfulSMul Q (integralClosure Q (FractionRing Q)) :=
    (faithfulSMul_iff_algebraMap_injective Q _).mpr (by
      intro x y h
      apply IsFractionRing.injective Q (FractionRing Q)
      have hh := congrArg (algebraMap (integralClosure Q (FractionRing Q))
        (FractionRing Q)) h
      simpa only [← IsScalarTower.algebraMap_apply] using hh)
  exact ⟨inferInstance, IsNoetherianRing.of_finite Q _, hnormal,
    Algebra.IsIntegral.comap_surjective Q _,
    RingHom.IsIntegral.ringKrullDim_le
      (algebraMap_isIntegral_iff.mpr
        (inferInstance : Algebra.IsIntegral Q (integralClosure Q (FractionRing Q))))⟩

/-- Noetherianity alone is not used as a normalization-finiteness premise:
the actual arithmetic base supplies Nagata before the three transformations. -/
theorem closed_component_normal_model_of_finiteType_int
    (R S L : Type u) [CommRing R] [CommRing S] [CommRing L]
    [Algebra.FiniteType ℤ R] [Algebra R S] [Module.Finite R S]
    [Algebra S L] (M : Submonoid S) [IsLocalization M L]
    (J : Ideal L) (p : minimalPrimes (L ⧸ J)) :
    Module.Finite ((L ⧸ J) ⧸ p.val)
      (integralClosure ((L ⧸ J) ⧸ p.val) (FractionRing ((L ⧸ J) ⧸ p.val))) ∧
    IsNoetherianRing
      (integralClosure ((L ⧸ J) ⧸ p.val) (FractionRing ((L ⧸ J) ⧸ p.val))) ∧
    IsIntegrallyClosed
      (integralClosure ((L ⧸ J) ⧸ p.val) (FractionRing ((L ⧸ J) ⧸ p.val))) ∧
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap ((L ⧸ J) ⧸ p.val)
        (integralClosure ((L ⧸ J) ⧸ p.val) (FractionRing ((L ⧸ J) ⧸ p.val))))) ∧
    ringKrullDim
      (integralClosure ((L ⧸ J) ⧸ p.val) (FractionRing ((L ⧸ J) ⧸ p.val))) ≤
      ringKrullDim ((L ⧸ J) ⧸ p.val) := by
  let : IsDomain ((L ⧸ J) ⧸ p.val) :=
    Algebra.minimalPrimeQuotient_isDomain _ p
  exact normal_model_of_nagata _
    (((IsNagataRing.of_finiteType_int R).finite_localized_quotient M J).quotient p.val)

end integralClosure
