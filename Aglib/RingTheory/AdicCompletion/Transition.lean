/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Power transitions and the algebra-valued completion evaluations

This is the ring-valued form of the native defining compatibility of the
completion's quotient coordinates.
-/

@[expose] public section

namespace AdicCompletion

/-- Algebra-valued evaluation commutes with the native quotient power transition. -/
theorem factorPow_evalₐ {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨f, rfl⟩ := mk_surjective I R x
  rw [evalₐ_mk, evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (f n) = Ideal.Quotient.mk (I ^ m) (f m)
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have h := SModEq.sub_mem.mp (f.property hmn).symm
  simpa only [smul_eq_mul, Ideal.mul_top] using h

end AdicCompletion
