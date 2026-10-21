module

import Aglib.RingTheory.Reflexive.AuslanderDimensionThree

universe u

open CategoryTheory

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = 3) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (e : Module.End R M ≃ₗ[R] (Fin r → M))
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) : Module.Free R M :=
  ModuleCat.free_of_endomorphism_equiv_of_free_punctured_of_dimension_three R hd M r e hfree

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R ≤ 2) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsReflexive R M] : Module.Free R M :=
  Module.free_of_isReflexive_of_dimension_le_two R hd M
