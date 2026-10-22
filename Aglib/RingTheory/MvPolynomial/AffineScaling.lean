/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Tactic.Ring

/-! # Jacobian rows under affine scaling

The polynomial chain rule needs no regularity. For a divided relation, cancellation
is performed only after evaluation in an algebra where the scale is regular.
-/

@[expose] public section

namespace MvPolynomial

variable {R S σ : Type*} [CommRing R] [CommRing S]

/-- The chain rule for simultaneous affine scaling of all variables. -/
theorem pderiv_aeval_affine_scaling (f : MvPolynomial σ R) (a : σ → R) (p : R)
    (i : σ) :
    pderiv i (aeval (fun j => C (a j) + C p * X j) f) =
      C p * aeval (fun j => C (a j) + C p * X j) (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp only [map_add, hf, hg, mul_add]
  | mul_X f j hf =>
    by_cases hji : j = i
    · subst j
      simp only [map_mul, aeval_X, pderiv_mul, map_add, pderiv_C,
        pderiv_X_self, zero_mul, zero_add, mul_one, hf]
      ring
    · simp only [map_mul, aeval_X, pderiv_mul, map_add, pderiv_C,
        pderiv_X_of_ne hji, zero_mul, mul_zero, add_zero, hf]
      ring

/-- The Jacobian row of a divided affine scaling equals the old row at the scaled point.
Regularity is required only in the algebra where the polynomials are evaluated. -/
theorem aeval_pderiv_of_affine_scaling_eq [Algebra R S]
    (f h : MvPolynomial σ R) (a : σ → R) (p : R)
    (hdiv : aeval (fun j => C (a j) + C p * X j) f = C p * h)
    (z : σ → S) (hp : IsRegular (algebraMap R S p)) (i : σ) :
    aeval z (pderiv i h) =
      aeval (fun j => algebraMap R S (a j) + algebraMap R S p * z j) (pderiv i f) := by
  have hd := congrArg (pderiv i) hdiv
  rw [pderiv_aeval_affine_scaling, pderiv_C_mul] at hd
  have he := congrArg (aeval z) hd
  simp only [map_mul, aeval_C, comp_aeval_apply, map_add, aeval_X] at he
  exact hp.left he.symm

end MvPolynomial
