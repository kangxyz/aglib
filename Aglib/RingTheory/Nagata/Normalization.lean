/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Defs
public import Aglib.RingTheory.IntegralClosure.CompleteCurve

/-!
# Finite normalization of reduced Nagata rings

The actual normalization embeds into the product of the normalizations
of the actual minimal-prime quotients. The Nagata condition supplies
finiteness of each component, and Noetherianity gives finiteness of the
embedded original normalization. No locality, completeness, or dimension
bound is needed.
-/

@[expose] public noncomputable section

universe u v

namespace integralClosure

/-- The literal normalization of a reduced Nagata ring in its supplied
total quotient ring is finite. The Nagata predicate uses auxiliary test
universe zero; the total quotient ring may lie in another universe. -/
theorem finite_of_isNagataRing
    (R : Type u) [CommRing R] [IsReduced R] (hR : IsNagataRing.{u, 0} R)
    (Q : Type v) [CommRing Q] [Algebra R Q] [IsFractionRing R Q] :
    Module.Finite R (integralClosure R Q) := by
  classical
  let : IsNoetherianRing R := hR.isNoetherianRing
  let : Fintype (minimalPrimes R) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := R)).fintype
  let : ∀ p : minimalPrimes R,
      Module.Finite R (integralClosure (R ⧸ p.val) (FractionRing (R ⧸ p.val))) :=
    fun p ↦ by
      let : p.val.IsPrime := p.property.isPrime
      let : Module.Finite (R ⧸ p.val)
          (integralClosure (R ⧸ p.val) (FractionRing (R ⧸ p.val))) :=
        (hR.isJapaneseRing_quotient p.val).finite_integralClosure
          (FractionRing (R ⧸ p.val))
      exact Module.Finite.trans (R ⧸ p.val)
        (integralClosure (R ⧸ p.val) (FractionRing (R ⧸ p.val)))
  exact Module.Finite.of_injective (toMinimalPrimeNormalizations R Q).toLinearMap
    (toMinimalPrimeNormalizations_injective R Q)

end integralClosure
