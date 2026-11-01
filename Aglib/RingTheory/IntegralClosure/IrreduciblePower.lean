/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! # Powers equal to an original irreducible element

Integral closedness lifts a positive-power root back to the original ring.
Irreducibility then forces exponent one; exponent zero is excluded directly.
No domain, discrete valuation, characteristic, finiteness or positivity hypothesis is needed.
-/

@[expose] public section

namespace IsIntegrallyClosedIn

universe u v

variable {R : Type u} [CommRing R]
  {S : Type v} [CommRing S] [Algebra R S] [IsIntegrallyClosedIn R S]

/-- An original irreducible element has no nontrivial power root in a
commutative algebra in which the base is integrally closed. Injectivity of the
original algebra map is part of the native integral-closure hypothesis. -/
theorem eq_one_of_pow_eq_irreducible {π : R} (hπ : Irreducible π)
    {x : S} {n : ℕ} (hx : x ^ n = algebraMap R S π) : n = 1 := by
  by_cases hn : n = 0
  · have hπone : π = 1 := IsIntegralClosure.algebraMap_injective R R S
      (by simpa [hn] using hx.symm)
    exact False.elim (hπ.not_isUnit (by rw [hπone]; exact isUnit_one))
  · have hint : IsIntegral R (x ^ n) := by
      rw [hx]
      exact isIntegral_algebraMap
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_isIntegral_pow (Nat.pos_of_ne_zero hn) hint
    have heq : r ^ n = π := IsIntegralClosure.algebraMap_injective R R S (by
      rw [map_pow, hr]
      exact hx)
    by_contra hne
    exact not_irreducible_pow hne (heq.symm ▸ hπ)

end IsIntegrallyClosedIn

namespace IsIntegrallyClosed

universe u v

variable {R : Type u} [CommRing R] [IsIntegrallyClosed R]
  {K : Type v} [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- The actual fraction-ring specialization of the integral-closure obstruction,
with no separate domain, field or positive-exponent hypothesis. -/
theorem eq_one_of_pow_eq_irreducible {π : R} (hπ : Irreducible π)
    {x : K} {n : ℕ} (hx : x ^ n = algebraMap R K π) : n = 1 :=
  IsIntegrallyClosedIn.eq_one_of_pow_eq_irreducible hπ hx

end IsIntegrallyClosed
