/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Support
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Support of finite-length modules over local rings

A finite-length module over a commutative local ring is supported at the closed
point. The statement includes the zero module and needs no Noetherian-ring
hypothesis. The proof specializes the existing maximal-support theorem.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A finite-length module over a local ring is supported on its closed point. -/
theorem support_subset_closedPoint_of_isFiniteLength
    {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    support R M ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) := by
  intro p hp
  have hm := isMaximal_of_mem_support_of_length_ne_top
    (Module.length_ne_top_iff.mpr hM) p hp
  exact (IsLocalRing.eq_maximalIdeal hm).symm.le

end Module
