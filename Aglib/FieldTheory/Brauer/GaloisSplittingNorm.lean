/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.GaloisDescent
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Determinant descent from a finite Galois matrix splitting

A specified splitting of the actual scalar extension produces a nonzero
homogeneous polynomial over the original field. Galois invariance is proved,
not assumed, by twisting the splitting on both sides and applying native
determinant invariance. Existence of a finite Galois splitting is not proved
in this leaf. The splitting field is explicitly infinite.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {K L A : Type*} [Field K] [Field L] [Algebra K L]
  [Ring A] [Algebra K A] {m n : ℕ}

/-- Twist a scalar-extension splitting by a coefficient-field automorphism on
both its source and target. The resulting equivalence is still `L`-linear. -/
def galoisTwistMatrixSplitting
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) (s : L ≃ₐ[K] L) :
    L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L where
  toRingEquiv := ((Algebra.TensorProduct.congr s.symm (AlgEquiv.refl : A ≃ₐ[K] A)).toRingEquiv.trans
    e.toRingEquiv).trans s.toRingEquiv.mapMatrix
  commutes' l := by
    change (e ((Algebra.TensorProduct.congr s.symm (AlgEquiv.refl : A ≃ₐ[K] A))
      (l ⊗ₜ[K] (1 : A)))).map s = algebraMap L (Matrix (Fin n) (Fin n) L) l
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    change (e (algebraMap L (L ⊗[K] A) (s.symm l))).map s = _
    rw [e.commutes]
    ext i j
    by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]

/-- The twist acts on the original algebra elements by coefficient conjugation. -/
theorem galoisTwistMatrixSplitting_one_tmul
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (s : L ≃ₐ[K] L) (a : A) :
    galoisTwistMatrixSplitting e s (1 ⊗ₜ[K] a) = (e (1 ⊗ₜ[K] a)).map s := by
  simp [galoisTwistMatrixSplitting]

/-- Coefficient conjugation of the determinant polynomial is the determinant
polynomial of the explicitly twisted splitting. -/
theorem map_matrixNormPolynomial_baseChange
    (b : Module.Basis (Fin m) K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) (s : L ≃ₐ[K] L) :
    MvPolynomial.map s.toRingHom (matrixNormPolynomial (b.baseChange L) e.toAlgHom) =
      matrixNormPolynomial (b.baseChange L) (galoisTwistMatrixSplitting e s).toAlgHom := by
  unfold matrixNormPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [galoisTwistMatrixSplitting_one_tmul]

/-- The actual splitting determinant polynomial is Galois invariant. -/
theorem matrixNormPolynomial_baseChange_fixed [Infinite L]
    (b : Module.Basis (Fin m) K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) (s : L ≃ₐ[K] L) :
    MvPolynomial.map s.toRingHom (matrixNormPolynomial (b.baseChange L) e.toAlgHom) =
      matrixNormPolynomial (b.baseChange L) e.toAlgHom := by
  rw [map_matrixNormPolynomial_baseChange]
  exact matrixNormPolynomial_eq_of_algEquiv (b.baseChange L) (galoisTwistMatrixSplitting e s) e

/-- An actual finite Galois matrix splitting supplies the descended nonzero
homogeneous norm polynomial, of degree equal to the matrix size. -/
theorem exists_normPolynomial_of_galois_splitting [Infinite L]
    [FiniteDimensional K L] [IsGalois K L]
    (b : Module.Basis (Fin m) K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    ∃ p : MvPolynomial (Fin m) K,
      MvPolynomial.map (algebraMap K L) p = matrixNormPolynomial (b.baseChange L) e.toAlgHom ∧
      p.IsHomogeneous n ∧ p ≠ 0 :=
  exists_matrixNormPolynomial_descent (b.baseChange L) e.toAlgHom
    (matrixNormPolynomial_baseChange_fixed b e)

end Algebra
