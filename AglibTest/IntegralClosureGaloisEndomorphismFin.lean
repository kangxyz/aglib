module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismFin

noncomputable section

variable (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]
  [Fintype (L ≃ₐ[K] L)]

example (h : Function.Surjective (IsIntegralClosure.galoisEndomorphism A K L B)) :
    Module.End A B ≃ₗ[A] (Fin (Fintype.card (L ≃ₐ[K] L)) → B) :=
  IsIntegralClosure.galoisEndomorphismFinEquiv A K L B h
