/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Original integral maps with common fractions

An integral extension of a normal domain with the same original fraction field
is the original ring. Degree one on compatible original fraction fields gives
this common-fraction condition, without local or completeness hypotheses.
-/

@[expose] public noncomputable section

namespace IsIntegrallyClosed

/-- An original integral map into a domain with the same fraction field is
bijective when the original base is integrally closed. -/
theorem bijective_algebraMap_of_common_fractionRing
    (R A K : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field K] [Algebra R A] [Algebra R K] [Algebra A K]
    [IsScalarTower R A K] [IsFractionRing R K] [IsFractionRing A K]
    [IsIntegrallyClosed R] [Algebra.IsIntegral R A] :
    Function.Bijective (algebraMap R A) := by
  constructor
  · intro r s hrs
    apply IsFractionRing.injective R K
    simpa only [IsScalarTower.algebraMap_apply R A K] using
      congrArg (algebraMap A K) hrs
  · intro a
    obtain ⟨r, hr⟩ := algebraMap_eq_of_integral
      (IsIntegral.algebraMap (B := K) (Algebra.IsIntegral.isIntegral (R := R) a))
    refine ⟨r, ?_⟩
    apply IsFractionRing.injective A K
    simpa only [IsScalarTower.algebraMap_apply R A K] using hr

/-- Degree one between the compatible original fraction fields gives bijectivity
of the original integral coefficient map. -/
theorem bijective_algebraMap_of_fraction_finrank_eq_one
    (R A K L : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra R A] [Algebra R K] [Algebra R L]
    [Algebra A L] [Algebra K L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsFractionRing R K] [IsFractionRing A L]
    [IsIntegrallyClosed R] [Algebra.IsIntegral R A]
    (hdegree : Module.finrank K L = 1) :
    Function.Bijective (algebraMap R A) := by
  let e : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegree)
  let : IsFractionRing R L := IsFractionRing.of_algEquiv (e.restrictScalars R)
  exact bijective_algebraMap_of_common_fractionRing R A L

end IsIntegrallyClosed
