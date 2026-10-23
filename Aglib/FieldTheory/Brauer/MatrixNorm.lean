/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The determinant polynomial of an actual matrix representation

For a finite basis of an algebra and a matrix representation, this constructs
the determinant of the generic linear combination. Its degree is the matrix
size, not the dimension of the algebra. Evaluation gives the original matrix
determinant. This is the polynomial construction needed before reduced-norm
coefficient descent; no descent or existence of a splitting is assumed here.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] {m n : ℕ}

/-- The literal determinant polynomial attached to a basis and a matrix representation. -/
def matrixNormPolynomial (b : Module.Basis (Fin m) K A)
    (f : A →ₐ[K] Matrix (Fin n) (Fin n) K) : MvPolynomial (Fin m) K :=
  Matrix.det (Matrix.of fun i j =>
    ∑ k, C (Matrix.entryLinearMap K K i j (f (b k))) * X k)

/-- The determinant polynomial is homogeneous of the matrix size. -/
theorem matrixNormPolynomial_isHomogeneous (b : Module.Basis (Fin m) K A)
    (f : A →ₐ[K] Matrix (Fin n) (Fin n) K) :
    (matrixNormPolynomial b f).IsHomogeneous n := by
  classical
  unfold matrixNormPolynomial
  rw [Matrix.det_apply']
  simp only [Matrix.of_apply, Matrix.entryLinearMap_apply]
  apply IsHomogeneous.sum
  intro s _
  have hp : (∏ i : Fin n, ∑ k : Fin m, C (f (b k) (s i) i) * X k).IsHomogeneous n := by
    simpa using IsHomogeneous.prod Finset.univ
      (fun i : Fin n => ∑ k : Fin m, C (f (b k) (s i) i) * X k) (fun _ => 1)
      (fun i _ => IsHomogeneous.sum Finset.univ _ 1
        (fun k _ => isHomogeneous_C_mul_X _ _))
  simpa only [map_intCast] using hp.C_mul ((Equiv.Perm.sign s : ℤ) : K)

/-- Evaluating basis coordinates gives the determinant of the original matrix image. -/
theorem eval_matrixNormPolynomial (b : Module.Basis (Fin m) K A)
    (f : A →ₐ[K] Matrix (Fin n) (Fin n) K) (x : Fin m → K) :
    eval x (matrixNormPolynomial b f) = (f (b.equivFun.symm x)).det := by
  classical
  change (eval x) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Module.Basis.equivFun_symm_apply, map_sum, Matrix.sum_apply,
    smul_eq_mul, mul_comm]

/-- A unit of the algebra cannot give a zero value of the determinant polynomial. -/
theorem eval_matrixNormPolynomial_ne_zero_of_isUnit (b : Module.Basis (Fin m) K A)
    (f : A →ₐ[K] Matrix (Fin n) (Fin n) K) (x : Fin m → K)
    (hx : IsUnit (b.equivFun.symm x)) : eval x (matrixNormPolynomial b f) ≠ 0 := by
  rw [eval_matrixNormPolynomial]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (hx.map f)).ne_zero

/-- A nontrivial zero of the constructed polynomial gives a genuine nonzero nonunit. -/
theorem exists_nonzero_nonunit_of_matrixNormPolynomial_zero
    (b : Module.Basis (Fin m) K A) (f : A →ₐ[K] Matrix (Fin n) (Fin n) K)
    (x : Fin m → K) (hx : x ≠ 0) (hz : eval x (matrixNormPolynomial b f) = 0) :
    ∃ a : A, a ≠ 0 ∧ ¬ IsUnit a := by
  refine ⟨b.equivFun.symm x, ?_, ?_⟩
  · intro h
    apply hx
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg b.equivFun h
  · intro hu
    exact eval_matrixNormPolynomial_ne_zero_of_isUnit b f x hu hz

end Algebra
