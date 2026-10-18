/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The rational-function change of variable `X ↦ X⁻¹`

Polynomial evaluation at the transcendental element `X⁻¹` extends to the
actual rational-function field. The extension fixes constants, swaps `X`
and `X⁻¹`, and is an involutive algebra equivalence.
-/

@[expose] public noncomputable section

namespace RatFunc

open Polynomial
open scoped nonZeroDivisors

variable (k : Type*) [Field k]

/-- The inverse of the rational-function variable is transcendental. -/
theorem transcendental_inv_X : Transcendental k (X⁻¹ : RatFunc k) := by
  intro h
  exact transcendental_X (IsAlgebraic.inv_iff.mp h)

/-- Substitution at the inverse variable preserves nonzero polynomial denominators. -/
theorem inversion_nonZeroDivisors :
    k[X]⁰ ≤ (RatFunc k)⁰.comap (aeval (X⁻¹ : RatFunc k)).toRingHom := by
  intro p hp
  change aeval (X⁻¹ : RatFunc k) p ∈ (RatFunc k)⁰
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  apply (mem_nonZeroDivisors_iff_ne_zero.mp hp)
  exact (transcendental_iff_injective.mp (transcendental_inv_X k))
    (h.trans (map_zero _).symm)

/-- The actual field homomorphism obtained by substituting `X⁻¹` for `X`. -/
def inversionHom : RatFunc k →+* RatFunc k :=
  liftRingHom (aeval (X⁻¹ : RatFunc k)).toRingHom (inversion_nonZeroDivisors k)

@[simp]
theorem inversionHom_C (a : k) : inversionHom k (C a) = C a := by
  simp [inversionHom]

@[simp]
theorem inversionHom_X : inversionHom k (X : RatFunc k) = X⁻¹ := by
  simp [inversionHom]

theorem inversionHom_inv_X : inversionHom k (X⁻¹ : RatFunc k) = X := by
  simp

/-- On every polynomial the field homomorphism is literal polynomial evaluation. -/
theorem inversionHom_algebraMap (p : k[X]) :
    inversionHom k (algebraMap k[X] (RatFunc k) p) = aeval (X⁻¹ : RatFunc k) p := by
  simp [inversionHom]

private theorem inversionHom_involutive_polynomial (p : k[X]) :
    inversionHom k (inversionHom k (algebraMap k[X] (RatFunc k) p)) =
      algebraMap k[X] (RatFunc k) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a => simp

/-- Applying the actual rational-function substitution twice is the identity. -/
theorem inversionHom_involutive : Function.Involutive (inversionHom k) := by
  intro f
  induction f using RatFunc.induction_on with
  | f p q _ =>
    simp only [map_div₀, inversionHom_involutive_polynomial]

/-- The involutive algebra automorphism that fixes constants and sends `X` to `X⁻¹`. -/
def inversion : RatFunc k ≃ₐ[k] RatFunc k where
  __ := inversionHom k
  invFun := inversionHom k
  left_inv := inversionHom_involutive k
  right_inv := inversionHom_involutive k
  commutes' := inversionHom_C k

@[simp]
theorem inversion_C (a : k) : inversion k (C a) = C a := inversionHom_C k a

@[simp]
theorem inversion_X : inversion k (X : RatFunc k) = X⁻¹ := inversionHom_X k

theorem inversion_inv_X : inversion k (X⁻¹ : RatFunc k) = X := inversionHom_inv_X k

@[simp]
theorem inversion_inversion (f : RatFunc k) : inversion k (inversion k f) = f :=
  inversionHom_involutive k f

end RatFunc
