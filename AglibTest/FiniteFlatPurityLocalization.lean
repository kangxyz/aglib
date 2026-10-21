/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.Etale.FiniteFlatPurityLocalization

/-! Checks of global finite-flat purity and the actual localized algebra endpoint. -/

open TensorProduct

example {R B : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    (hgeneric : Algebra.Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Algebra.Etale (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] B)) : Algebra.Etale R B :=
  Algebra.etale_of_generic_and_height_one_etale hgeneric hcodim

example {R B : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    (hgeneric : Algebra.Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Algebra.Etale (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] B)) (p : PrimeSpectrum R) :
    Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] B) :=
  Algebra.etale_atPrime_of_generic_and_height_one_etale hgeneric hcodim p

example (K : Type*) [Field K] : Algebra.Etale K (Fin 0 → K) :=
  Algebra.etale_of_generic_and_height_one_etale inferInstance (fun _ _ ↦ inferInstance)
