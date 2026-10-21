module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismLocalEtale

noncomputable section

variable (A K L D : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [Field K] [Field L] [CommRing D] [IsDomain D]
  [IsDiscreteValuationRing D] [Algebra A D]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra D K] [IsFractionRing D K]
  [Algebra D L] [IsScalarTower D K L] [IsScalarTower A D L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
  (M : Submonoid A) [IsLocalization M D]
  [Algebra.Etale D (integralClosure D L)]

example : Function.Surjective (LocalizedModule.map M
    ((IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)).restrictScalars A)) :=
  integralClosure.galoisEndomorphism_localized_surjective_of_etale A K L D M
