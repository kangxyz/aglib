module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismHartogs

noncomputable section

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
  [Fintype (L ≃ₐ[K] L)]

example (hloc : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
    Function.Surjective (LocalizedModule.map p.primeCompl
      ((IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)).restrictScalars A))) :
    Function.Surjective (IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)) :=
  IsIntegralClosure.galoisEndomorphism_surjective_of_localized_height_one
    A K L (integralClosure A L) hloc
