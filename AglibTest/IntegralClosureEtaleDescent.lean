module

import Aglib.RingTheory.IntegralClosure.EtaleDescent

noncomputable section

variable (A K L E : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra.IsIntegral K L]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Algebra.Etale A (integralClosure A L)]
  [Module.FaithfullyFlat A (integralClosure A L)]

example (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) :
    Algebra.Etale A (integralClosure A E) :=
  integralClosure.etale_of_faithfullyFlat_splitting_normalization A K L E hsplit

omit [Module.FaithfullyFlat A (integralClosure A L)] in
example (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) :
    Algebra.Etale A (integralClosure A E) :=
  integralClosure.etale_of_splitting_normalization A K L E hsplit
