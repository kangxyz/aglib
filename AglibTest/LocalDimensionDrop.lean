/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.LocalDrop

/-! Natural-number dimension descent without Noetherianity or catenarity. -/

@[expose] public section

variable {R : Type*} [CommRing R] [IsLocalRing R]

example (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (p : PrimeSpectrum R)
    (hp : p.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, n < d ∧ ringKrullDim (Localization.AtPrime p.asIdeal) = (n : ℕ) :=
  IsLocalRing.exists_ringKrullDim_localization_lt d hd p hp

example (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (p : PrimeSpectrum R)
    (hp : p.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    ringKrullDim (Localization.AtPrime p.asIdeal) < (d : ℕ) :=
  IsLocalRing.ringKrullDim_localization_lt d hd p hp
