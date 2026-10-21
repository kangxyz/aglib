module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismBaseChange

noncomputable section

variable (A K L B D S : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [CommRing D] [CommRing S]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]
  [Algebra A D] [Algebra D K] [IsFractionRing D K] [Algebra D L]
  [IsScalarTower D K L] [Algebra D S] [Algebra S L]
  [IsScalarTower D S L] [IsIntegralClosure S D L]
  [Algebra B S] [IsScalarTower B S L]
  [Algebra A S] [IsScalarTower A B S] [IsScalarTower A D S]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
  (M : Submonoid A) [IsLocalization M D]
  [IsLocalizedModule M (IsScalarTower.toAlgHom A B S).toLinearMap]
  [Module.FinitePresentation A B] [IsNoetherianRing D]
  [Module.Free D S] [Module.Finite D S] [Algebra.Etale D S]

example : Function.Surjective (LocalizedModule.map M
    ((IsIntegralClosure.galoisEndomorphism A K L B).restrictScalars A)) :=
  IsIntegralClosure.galoisEndomorphism_localizedModule_surjective_of_etale A K L B D S M

example :
    IsLocalizedModule.map M (IsIntegralClosure.galoisCoefficientBaseChange A K L B S)
      (IsIntegralClosure.galoisEndomorphismBaseChange A B D S M)
      ((IsIntegralClosure.galoisEndomorphism A K L B).restrictScalars A) =
        (IsIntegralClosure.galoisEndomorphism D K L S).restrictScalars A :=
  IsIntegralClosure.galoisEndomorphism_baseChange_eq A K L B D S M
