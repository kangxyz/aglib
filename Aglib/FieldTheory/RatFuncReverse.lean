/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.RatFuncInversion
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Polynomial reversal under rational-function inversion

The actual substitution `X ↦ X⁻¹` sends a polynomial to its reversed
polynomial multiplied by `X⁻¹` to the original natural degree. The identity
holds over every field, also for constants and the zero polynomial.
-/

@[expose] public noncomputable section

namespace RatFunc

open Polynomial

variable (k : Type*) [Field k]

/-- Literal polynomial substitution at `X⁻¹`, expressed using reversal. -/
theorem inversion_algebraMap_reverse (p : k[X]) :
    inversion k (algebraMap k[X] (RatFunc k) p) =
      (X⁻¹ : RatFunc k) ^ p.natDegree * algebraMap k[X] (RatFunc k) p.reverse := by
  let : Invertible (X⁻¹ : RatFunc k) := invertibleOfNonzero (inv_ne_zero X_ne_zero)
  have h := Polynomial.eval₂_reverse_mul_pow (algebraMap k (RatFunc k))
    (X⁻¹ : RatFunc k) p
  rw [invOf_eq_inv, inv_inv, ← aeval_def, aeval_X_left_eq_algebraMap,
    ← aeval_def] at h
  change inversionHom k _ = _
  rw [inversionHom_algebraMap, ← h, mul_comm]

end RatFunc
