/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.Etale.FiniteFlatPurity

/-! Checks of the finite-algebra trace criterion, including empty products. -/

open Module TensorProduct

example (K : Type*) [Field K] :
    (Algebra.traceForm K (Fin 0 → K)).Nondegenerate :=
  Algebra.etale_iff_traceForm_nondegenerate.mp inferInstance

example (K : Type*) [Field K] :
    (Algebra.traceForm K (Fin 2 → K)).Nondegenerate :=
  Algebra.etale_iff_traceForm_nondegenerate.mp inferInstance

example {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (h : (Algebra.traceForm K B).Nondegenerate) {x : B} (hx : IsNilpotent x) : x = 0 := by
  have := Algebra.isReduced_of_traceForm_nondegenerate h
  exact hx.eq_zero

example {R B ι : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R B)
    (h : IsUnit (Algebra.discr R b)) : Algebra.Etale R B :=
  (Algebra.etale_iff_isUnit_discr_of_basis b).mpr h

example {R B ι : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R B) [Algebra.Etale R B] :
    IsUnit (Algebra.discr R b) :=
  (Algebra.etale_iff_isUnit_discr_of_basis b).mp inferInstance

example {R B ι : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Finite ι] (b : Basis ι R B)
    (hgeneric : Algebra.Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Algebra.Etale (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] B)) : Algebra.Etale R B :=
  Algebra.etale_of_generic_and_height_one_etale_of_basis b hgeneric hcodim

example {R B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] [Algebra.Etale R B] :
    Function.Surjective (Algebra.traceForm R B) :=
  Algebra.traceForm_surjective_of_etale

example {R B : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    (hgeneric : Algebra.Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Algebra.Etale (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] B)) : Algebra.Etale R B :=
  Algebra.etale_of_generic_and_height_one_etale_of_isLocalRing hgeneric hcodim
