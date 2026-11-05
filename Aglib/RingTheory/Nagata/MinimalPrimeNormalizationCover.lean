/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.ClosedSupportNormalization

/-! # The complete finite normal-component cover

The product includes every literal minimal-prime quotient and its normalization
in its own fraction field. Nagata, rather than Noetherianity alone, supplies
finiteness. Every original prime lifts to this actual product; no component or
point is discarded. All component dimensions retain the original ring bound.
-/

@[expose] public noncomputable section
namespace Algebra
universe u
variable (R : Type u) [CommRing R]

/-- The literal normalization of one actual minimal-prime quotient. -/
abbrev minimalPrimeNormalization (p : minimalPrimes R) :=
  integralClosure (R ⧸ p.val) (FractionRing (R ⧸ p.val))

/-- The base-ring action factors through the specified minimal-prime quotient. -/
instance minimalPrimeNormalizationBaseAlgebra (p : minimalPrimes R) :
    Algebra R (minimalPrimeNormalization R p) :=
  ((algebraMap (R ⧸ p.val) (minimalPrimeNormalization R p)).comp
    (Ideal.Quotient.mk p.val)).toAlgebra

instance minimalPrimeNormalization_scalarTower (p : minimalPrimes R) :
    IsScalarTower R (R ⧸ p.val) (minimalPrimeNormalization R p) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The complete product, with the diagonal map from the original ring. -/
abbrev minimalPrimeNormalizationProduct :=
  (p : minimalPrimes R) → minimalPrimeNormalization R p

/-- Each actual normalized component is finite, normal, and has the original
component's dimension bound. -/
theorem minimalPrimeNormalization_properties
    (hR : IsNagataRing.{u, 0} R) (p : minimalPrimes R) :
    Module.Finite R (minimalPrimeNormalization R p) ∧
    IsNoetherianRing (minimalPrimeNormalization R p) ∧
    IsDomain (minimalPrimeNormalization R p) ∧
    IsIntegrallyClosed (minimalPrimeNormalization R p) ∧
    ringKrullDim (minimalPrimeNormalization R p) ≤ ringKrullDim R := by
  let : IsDomain (R ⧸ p.val) := minimalPrimeQuotient_isDomain R p
  obtain ⟨hfin, hnoeth, hnormal, _, hdim⟩ :=
    integralClosure.normal_model_of_nagata (R ⧸ p.val) (hR.quotient p.val)
  let : Module.Finite (R ⧸ p.val) (minimalPrimeNormalization R p) := hfin
  exact ⟨Module.Finite.trans (R ⧸ p.val) (minimalPrimeNormalization R p),
    hnoeth, inferInstance, hnormal,
    hdim.trans (minimalPrimeQuotient_ringKrullDim_le R p)⟩

/-- Nagata makes the product of all actual normal components finite. -/
theorem minimalPrimeNormalizationProduct_finite (hR : IsNagataRing.{u, 0} R) :
    Module.Finite R (minimalPrimeNormalizationProduct R) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let : Fintype (minimalPrimes R) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := R)).fintype
  let : ∀ p : minimalPrimes R, Module.Finite R (minimalPrimeNormalization R p) :=
    fun p => (minimalPrimeNormalization_properties R hR p).1
  infer_instance

/-- Every original prime lifts through a containing minimal component and its
actual normalization, then through the actual product evaluation map. -/
theorem minimalPrimeNormalizationProduct_comap_surjective
    (hR : IsNagataRing.{u, 0} R) :
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap R (minimalPrimeNormalizationProduct R))) := by
  intro q
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
    (show (⊥ : Ideal R) ≤ q.asIdeal from bot_le)
  have hq : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p)) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact hpq
  obtain ⟨q', hq'⟩ := hq
  let pm : minimalPrimes R := ⟨p, hp⟩
  let : IsDomain (R ⧸ p) := minimalPrimeQuotient_isDomain R pm
  have hsur := (integralClosure.normal_model_of_nagata
    (R ⧸ p) (hR.quotient p)).2.2.2.1
  obtain ⟨q'', hq''⟩ := hsur q'
  let ev : minimalPrimeNormalizationProduct R →+* minimalPrimeNormalization R pm :=
    Pi.evalRingHom (fun p : minimalPrimes R => minimalPrimeNormalization R p) pm
  refine ⟨PrimeSpectrum.comap ev q'', ?_⟩
  change PrimeSpectrum.comap (Ideal.Quotient.mk p)
    (PrimeSpectrum.comap (algebraMap (R ⧸ p)
      (minimalPrimeNormalization R pm)) q'') = q
  exact (congrArg (PrimeSpectrum.comap (Ideal.Quotient.mk p)) hq'').trans hq'

/-- The whole finite cover also retains the original support bound. -/
theorem minimalPrimeNormalizationProduct_ringKrullDim_le
    (hR : IsNagataRing.{u, 0} R) :
    ringKrullDim (minimalPrimeNormalizationProduct R) ≤ ringKrullDim R := by
  let : Module.Finite R (minimalPrimeNormalizationProduct R) :=
    minimalPrimeNormalizationProduct_finite R hR
  exact RingHom.IsIntegral.ringKrullDim_le
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral R (minimalPrimeNormalizationProduct R)))

end Algebra
