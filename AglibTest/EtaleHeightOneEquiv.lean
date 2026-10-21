module

import Aglib.RingTheory.Etale.HeightOneEquiv

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

example (e : B ≃ₐ[A] C)
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → Algebra.IsUnramifiedAt A q.asIdeal) :
    ∀ q : PrimeSpectrum C, q.asIdeal.height = 1 → Algebra.IsUnramifiedAt A q.asIdeal :=
  Algebra.unramified_height_one_of_equiv e h
