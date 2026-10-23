/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Support
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Finite torsion modules in dimension at most one

A finite torsion module over a Noetherian ring of dimension at most one has
finite length. Torsion is taken with respect to the actual non-zero-divisors;
the ring need not be a domain or a local ring.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite torsion module has finite length in dimension at most one,
including over rings with several minimal primes. -/
theorem finiteLength_of_isTorsion [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Module.Finite R M] (hM : IsTorsion R M) : IsFiniteLength R M := by
  obtain ⟨a, ha, haRegular⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  apply finiteLength_of_support_maximal R M
  intro p hp
  rcases Ring.krullDimLE_one_iff.mp (inferInstance : Ring.KrullDimLE 1 R)
      p.asIdeal p.isPrime with hmin | hmax
  · have haAnn : a ∈ Module.annihilator R M := by
      simpa only [Submodule.annihilator_top, SetLike.mem_coe] using ha
    exact False.elim
      (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
        (Module.annihilator_le_of_mem_support hp haAnn) hmin haRegular)
  · exact hmax

end Module
