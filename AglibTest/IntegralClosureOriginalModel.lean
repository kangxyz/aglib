module

import Aglib.RingTheory.IntegralClosure.OriginalModel

noncomputable section

section HeightOne

variable (A B E : Type*) [CommRing A] [CommRing B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Field E] [Algebra B E] [IsFractionRing B E] [Algebra A E] [IsScalarTower A B E]

example : IsIntegralClosure B A E := inferInstance

example (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → Algebra.IsUnramifiedAt A q.asIdeal) :
    ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A q.asIdeal :=
  IsIntegralClosure.unramified_height_one_normalization A B E h

end HeightOne

variable (A B K L E : Type*) [CommRing A] [IsDomain A]
  [CommRing B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsIntegral K L]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [Algebra B E] [IsFractionRing B E] [IsScalarTower A B E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Algebra.Etale A (integralClosure A L)]

example (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) : Algebra.Etale A B :=
  Algebra.etale_of_splitting_normalization A B K L E hsplit
