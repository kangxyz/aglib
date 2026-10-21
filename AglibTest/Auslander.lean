module

import Aglib.RingTheory.Reflexive.Auslander

universe u

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (e : Module.End R M ≃ₗ[R] (Fin r → M))
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) : Module.Free R M :=
  ModuleCat.free_of_endomorphism_equiv_of_free_punctured R M r e hfree

example (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = (d : ℕ))
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (e : Module.End R M ≃ₗ[R] (Fin r → M))
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) : Module.Free R M :=
  ModuleCat.free_of_endomorphism_equiv_of_free_punctured_of_dimension d R hd M r e hfree
