/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.PrincipalOpen
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Detecting units in codimension one

A nonzero nonunit in a Noetherian domain belongs to a height-one prime.
Consequently a nonzero element is a unit if and only if it becomes a unit in
all height-one localizations. The nonzero hypothesis is necessary, including
when the ring is a field and has no height-one primes.

These scalar criteria are inputs to the discriminant proof of finite-flat
purity. They do not assert flatness or purity for an arbitrary finite algebra.
-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

namespace Ideal

/-- A nonzero nonunit of a Noetherian domain lies in a height-one prime. -/
theorem exists_height_one_prime_mem {x : R} (hx : x ≠ 0) (hunit : ¬ IsUnit x) :
    ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ x ∈ P := by
  have hproper : Ideal.span {x} ≠ ⊤ := fun h =>
    hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hproper
  exact ⟨P, hP.isPrime, height_eq_one_of_mem_minimalPrimes_span hx hP,
    hP.le (Ideal.mem_span_singleton_self x)⟩

end Ideal

/-- A nonzero scalar is a unit if it avoids all height-one primes. -/
theorem isUnit_of_not_mem_height_one_primes {x : R} (hx : x ≠ 0)
    (h : ∀ P : Ideal R, P.IsPrime → P.height = 1 → x ∉ P) : IsUnit x := by
  by_contra hunit
  obtain ⟨P, hP, hheight, hxP⟩ := Ideal.exists_height_one_prime_mem hx hunit
  exact h P hP hheight hxP

/-- A nonzero scalar is a unit exactly when it is a unit at every height-one
localization. The nonzero hypothesis also covers zero-dimensional domains. -/
theorem isUnit_iff_isUnit_at_height_one {x : R} (hx : x ≠ 0) :
    IsUnit x ↔ ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) x) := by
  constructor
  · intro h p _
    exact h.map (algebraMap R (Localization.AtPrime p.asIdeal))
  · intro h
    apply isUnit_of_not_mem_height_one_primes hx
    intro P hP hheight
    let : P.IsPrime := hP
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P x).mp
      (h ⟨P, hP⟩ hheight)
