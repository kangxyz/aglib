/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Height one at minimal primes over a nonzerodivisor


Source: `R5Lab.Aglib.RingTheory.Ideal.HeightOne`.
Packet SHA-256:
`19d107b3d1557283987ca078e9a37e9871d4dc726ddd05b663dd9c303ef9da5c`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

universe u
namespace Ideal

/-- The numerical height is proved by the existing Krull principal ideal
 theorem plus its nonzerodivisor lower bound. -/
theorem minimalPrime_height_one {A : Type u} [CommRing A] [IsNoetherianRing A]
    {a : A} (ha : a ∈ nonZeroDivisors A) {p : Ideal A}
    (hp : p ∈ (Ideal.span {a}).minimalPrimes) : p.height = 1 :=
  le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ha).trans
      (Ideal.height_mono hp.le))

end Ideal
