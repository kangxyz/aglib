/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.KrullDimension.UnitDetection

/-! Tests for scalar unit detection in height-one localizations. -/

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

example {x : R} (hx : x ≠ 0)
    (h : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) x)) : IsUnit x :=
  (isUnit_iff_isUnit_at_height_one hx).mpr h

example {x : R} (hx : x ≠ 0) (h : ¬ IsUnit x) :
    ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ x ∈ P :=
  Ideal.exists_height_one_prime_mem hx h

end
