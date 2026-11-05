/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Aglib.RingTheory.KrullDimension.FiniteClosedSupport

/-! # The actual finite product of minimal-prime quotient domains

The diagonal algebra map to the product of the original minimal-prime
quotients has surjective spectrum, even for nonreduced rings. No reducedness,
normality, choice of a component containing a prescribed point, or covering
certificate is assumed. Noetherianity is used only for finiteness of the
product, not for spectrum surjectivity.
-/

@[expose] public noncomputable section

namespace Algebra

universe u
variable (R : Type u) [CommRing R]

/-- The literal product of the quotient domains, with its native diagonal
R-algebra structure. -/
abbrev minimalPrimeQuotientProduct := (p : minimalPrimes R) → R ⧸ p.val

/-- Each original factor is a domain, including when R has nilpotents. -/
theorem minimalPrimeQuotient_isDomain (p : minimalPrimes R) :
    IsDomain (R ⧸ p.val) := by
  let : p.val.IsPrime := p.property.isPrime
  infer_instance

/-- Every prime downstairs lifts through an actual minimal-prime factor and
then through the actual product evaluation map. -/
theorem minimalPrimeQuotientProduct_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap R (minimalPrimeQuotientProduct R))) := by
  intro q
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
    (show (⊥ : Ideal R) ≤ q.asIdeal from bot_le)
  have hq : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p)) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact hpq
  obtain ⟨q', hq'⟩ := hq
  let e : minimalPrimeQuotientProduct R →+* R ⧸ p :=
    Pi.evalRingHom (fun p : minimalPrimes R => R ⧸ p.val) ⟨p, hp⟩
  refine ⟨PrimeSpectrum.comap e q', ?_⟩
  change PrimeSpectrum.comap (Ideal.Quotient.mk p) q' = q
  exact hq'

/-- Noetherianity makes the actual product finite over R. -/
theorem minimalPrimeQuotientProduct_finite [IsNoetherianRing R] :
    Module.Finite R (minimalPrimeQuotientProduct R) := by
  let : Fintype (minimalPrimes R) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := R)).fintype
  infer_instance

/-- Passing to the literal component does not increase the induction rank. -/
theorem minimalPrimeQuotient_ringKrullDim_le (p : minimalPrimes R) :
    ringKrullDim (R ⧸ p.val) ≤ ringKrullDim R :=
  RingHom.IsIntegral.ringKrullDim_le
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral R (R ⧸ p.val)))

/-- The actual finite product also retains the original bound. -/
theorem minimalPrimeQuotientProduct_ringKrullDim_le [IsNoetherianRing R] :
    ringKrullDim (minimalPrimeQuotientProduct R) ≤ ringKrullDim R := by
  let : Module.Finite R (minimalPrimeQuotientProduct R) :=
    minimalPrimeQuotientProduct_finite R
  exact RingHom.IsIntegral.ringKrullDim_le
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral R (minimalPrimeQuotientProduct R)))

end Algebra
