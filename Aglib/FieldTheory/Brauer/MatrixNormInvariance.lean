/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.MatrixNorm
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Independence and zero locus of the matrix norm polynomial

The original determinant polynomial is independent of a chosen actual matrix
splitting over an infinite field. Its zero locus is exactly the nonunit locus.
The infinite-field hypothesis is used only to recover polynomial equality from
all evaluations. No assertion of existence of a splitting is made here.
-/

@[expose] public noncomputable section

namespace Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] {m n r : ℕ}

/-- A unital matrix representation gives a nonzero determinant polynomial. -/
theorem matrixNormPolynomial_ne_zero (b : Module.Basis (Fin m) K A)
    (f : A →ₐ[K] Matrix (Fin n) (Fin n) K) : matrixNormPolynomial b f ≠ 0 := by
  intro hz
  have h := eval_matrixNormPolynomial b f (b.equivFun 1)
  rw [hz] at h
  simp at h

/-- For an actual matrix splitting, polynomial vanishing detects precisely the original nonunits. -/
theorem eval_matrixNormPolynomial_eq_zero_iff (b : Module.Basis (Fin m) K A)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) (x : Fin m → K) :
    MvPolynomial.eval x (matrixNormPolynomial b e.toAlgHom) = 0 ↔
      ¬ IsUnit (b.equivFun.symm x) := by
  rw [eval_matrixNormPolynomial, ← MulEquiv.isUnit_map e,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact not_not.symm

/-- Over an infinite field the polynomial does not depend on the actual matrix splitting. -/
theorem matrixNormPolynomial_eq_of_algEquiv [Infinite K]
    (b : Module.Basis (Fin m) K A)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (e' : A ≃ₐ[K] Matrix (Fin r) (Fin r) K) :
    matrixNormPolynomial b e.toAlgHom = matrixNormPolynomial b e'.toAlgHom := by
  apply MvPolynomial.funext
  intro x
  rw [eval_matrixNormPolynomial, eval_matrixNormPolynomial]
  simpa using (Matrix.det_map (e.symm.trans e') (e (b.equivFun.symm x))).symm

end Algebra
