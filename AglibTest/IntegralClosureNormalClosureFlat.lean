module

import Aglib.RingTheory.IntegralClosure.NormalClosureFlat
import Mathlib.FieldTheory.IsSepClosed

universe u

example (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    (E : Type (u + 1)) [Field E] [Algebra (FractionRing A) E] [Algebra A E]
    [IsScalarTower A (FractionRing A) E]
    [FiniteDimensional (FractionRing A) E] [Algebra.IsSeparable (FractionRing A) E]
    [Algebra A (SeparableClosure (FractionRing A))]
    [IsScalarTower A (FractionRing A) (SeparableClosure (FractionRing A))]
    [Module.Flat A (integralClosure A
      (IntermediateField.normalClosure (FractionRing A) E (SeparableClosure (FractionRing A))))]
    (h : ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A q.asIdeal) :
    Algebra.Etale A (integralClosure A
      (IntermediateField.normalClosure (FractionRing A) E (SeparableClosure (FractionRing A)))) :=
  integralClosure.normalClosure_etale_of_flat A E (SeparableClosure (FractionRing A)) h
