/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.EtaleDescent
public import Aglib.RingTheory.Etale.HeightOneEquiv

/-!
# Returning normalization statements to the original finite normal algebra

The native integral-closure instance identifies a finite normal domain with the
normalization in its own fraction field. The comparisons below are over the
original base algebra, not an abstract ring isomorphism.
-/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (A B E : Type*) [CommRing A] [CommRing B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Field E] [Algebra B E] [IsFractionRing B E] [Algebra A E] [IsScalarTower A B E]

/-- The height-one hypothesis on the original finite normal algebra transfers
along its canonical normalization equivalence. -/
theorem unramified_height_one_normalization
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → Algebra.IsUnramifiedAt A q.asIdeal) :
    ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A q.asIdeal :=
  Algebra.unramified_height_one_of_equiv
    (IsIntegralClosure.equiv A B E (integralClosure A E)) h

end IsIntegralClosure

namespace Algebra

variable (A B K L E : Type*) [CommRing A] [IsDomain A]
  [CommRing B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsIntegral K L]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [Algebra B E] [IsFractionRing B E] [IsScalarTower A B E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Etale A (integralClosure A L)]

/-- Etaleness of an upper splitting normalization descends to the actual given
finite normal algebra. No flatness of that algebra is assumed. -/
theorem etale_of_splitting_normalization
    (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) : Etale A B := by
  let : Etale A (integralClosure A E) :=
    integralClosure.etale_of_splitting_normalization A K L E hsplit
  exact Etale.of_equiv (IsIntegralClosure.equiv A (integralClosure A E) E B)

end Algebra
