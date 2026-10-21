/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismUnramified
public import Aglib.RingTheory.Etale.FiniteFlatPurityLocalization

/-! Finite-flat purity for the actual normal-closure normalization. -/

@[expose] public section

noncomputable section

namespace integralClosure

variable (A E Ω : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A]
  [Field E] [Algebra (FractionRing A) E] [Algebra A E]
  [IsScalarTower A (FractionRing A) E]
  [FiniteDimensional (FractionRing A) E] [Algebra.IsSeparable (FractionRing A) E]
  [Field Ω] [Algebra (FractionRing A) Ω] [Algebra A Ω]
  [IsScalarTower A (FractionRing A) Ω] [IsGalois (FractionRing A) Ω]

local notation "N" => IntermediateField.normalClosure (FractionRing A) E Ω

/-- Once flatness of the actual upper normalization is supplied, source
height-one unramifiedness makes it etale. The generic and local models are
canonical; the missing Auslander flatness is not hidden in this statement. -/
theorem normalClosure_etale_of_flat
    [Module.Flat A (integralClosure A N)]
    (h : ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A q.asIdeal) : Algebra.Etale A (integralClosure A N) := by
  let : Module.Finite A (integralClosure A N) :=
    IsIntegralClosure.finite A (FractionRing A) N (integralClosure A N)
  let : Algebra.Etale (FractionRing A) N :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable _ _
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  exact Algebra.etale_of_generic_and_height_one_etale
    (Algebra.Etale.of_equiv (genericFiberEquiv A (FractionRing A) N).symm)
    (fun p hp => normalClosure_etale_atPrime_tensor_of_source_height_one
      A (FractionRing A) E Ω h p.asIdeal hp)

end integralClosure
