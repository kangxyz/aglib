/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Cartier quotient length and normalized DVR order

For the specified nonzero element of a discrete valuation ring, its actual
principal quotient length is the normalized additive valuation. No uniformizer
is part of the statement, and repeated vanishing is retained. This module has
only Mathlib dependencies.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual principal quotient length equals the normalized DVR order of
the specified scalar, including its full multiplicity. -/
theorem length_quotient_span_eq_addVal (t : R) (ht : t ≠ 0) :
    Module.length R (R ⧸ Ideal.span {t}) = addVal R t := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible ht hϖ
  rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    length_quotient_pow_maximalIdeal, addVal_def' u hϖ]

/-- Singleton Cartier equations use the same actual quotient and normalized
DVR order. This form composes directly with the endpoint-fiber length API. -/
theorem length_quotient_ofList_eq_addVal (t : R) (ht : t ≠ 0) :
    Module.length R (R ⧸ Ideal.ofList [t]) = addVal R t := by
  rw [Ideal.ofList_singleton]
  exact length_quotient_span_eq_addVal t ht

end IsDiscreteValuationRing
