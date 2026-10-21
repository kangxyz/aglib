/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.Etale.CodimensionOne

/-! Checks for native source unramifiedness and the actual finite base-localized model. -/

open TensorProduct

example {R B : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CommRing B] [IsDomain B] [Algebra R B]
    [FaithfulSMul R B] [Module.Finite R B]
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R q.asIdeal)
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] B) :=
  Algebra.etale_atPrime_tensor_of_height_one h p hp

example {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (h : ∀ (q : Ideal B) [q.IsMaximal], Algebra.IsUnramifiedAt R q) :
    Algebra.FormallyUnramified R B :=
  Algebra.formallyUnramified_of_isUnramifiedAt_maximal h

example {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.EssFiniteType R B] (p : Ideal R) [p.IsPrime]
    (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)] :
    Algebra.IsUnramifiedAt R q ↔
      Algebra.IsSeparable p.ResidueField q.ResidueField ∧
        p.map (algebraMap R (Localization.AtPrime q)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
  Algebra.isUnramifiedAt_iff_map_eq R p q

example {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p (Localization.AtPrime p) hp
