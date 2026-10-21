module

import Aglib.RingTheory.Etale.ZariskiNagataPurity

universe u v w

variable (A : Type u) [CommRing A] [IsDomain A] [IsRegularRing A]
  (B : Type v) [CommRing B] [IsIntegrallyClosed B]
  [Algebra A B] [Module.Finite A B]
  (E : Type w) [Field E] [Algebra B E] [IsFractionRing B E]
  [Algebra A E] [IsScalarTower A B E]
  [Algebra (FractionRing A) E] [IsScalarTower A (FractionRing A) E]
  [Algebra.IsSeparable (FractionRing A) E]

example (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → Algebra.IsUnramifiedAt A q.asIdeal) :
    Algebra.Etale A B :=
  Algebra.etale_of_unramified_height_one_of_isRegularRing A B E h

/-- Fixed successor universe levels cannot collapse to the base universe. -/
example (R : Type u) [CommRing R] [IsDomain R] [IsRegularRing R]
    (S : Type (u + 1)) [CommRing S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (F : Type (u + 2)) [Field F] [Algebra S F] [IsFractionRing S F]
    [Algebra R F] [IsScalarTower R S F]
    [Algebra (FractionRing R) F] [IsScalarTower R (FractionRing R) F]
    [Algebra.IsSeparable (FractionRing R) F]
    (h : ∀ q : PrimeSpectrum S, q.asIdeal.height = 1 → Algebra.IsUnramifiedAt R q.asIdeal) :
    Algebra.Etale R S :=
  Algebra.etale_of_unramified_height_one_of_isRegularRing R S F h

section CanonicalFractionFields

attribute [local instance] FractionRing.liftAlgebra

example (R : Type u) [CommRing R] [IsDomain R] [IsRegularRing R]
    (S : Type (u + 1)) [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (h : ∀ q : PrimeSpectrum S, q.asIdeal.height = 1 → Algebra.IsUnramifiedAt R q.asIdeal) :
    Algebra.Etale R S :=
  Algebra.etale_of_unramified_height_one R S h

end CanonicalFractionFields
