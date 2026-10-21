module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismUnramified
import Mathlib.FieldTheory.IsSepClosed

open scoped TensorProduct

noncomputable section

variable (A K E : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Algebra A (SeparableClosure K)] [IsScalarTower A K (SeparableClosure K)]

local notation "N" => IntermediateField.normalClosure K E (SeparableClosure K)


example (h : ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
    Algebra.IsUnramifiedAt A q.asIdeal) :
    Function.Surjective (IsIntegralClosure.galoisEndomorphism A K N (integralClosure A N)) :=
  integralClosure.normalClosure_galoisEndomorphism_surjective A K E (SeparableClosure K) h

example (h : ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
    Algebra.IsUnramifiedAt A q.asIdeal)
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] integralClosure A N) :=
  integralClosure.normalClosure_etale_atPrime_tensor_of_source_height_one
    A K E (SeparableClosure K) h p hp
