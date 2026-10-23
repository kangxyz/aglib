/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Split central simple algebras and the native Brauer quotient

These results use Mathlib's `CSA`, `IsBrauerEquivalent` and `BrauerGroup`.
The latter is currently a quotient, without a group structure. The scalar
representative and quotient comparisons here do not introduce a replacement.
-/

@[expose] public noncomputable section

universe u

namespace CSA

variable (K : Type u) [Field K]

/-- The scalar algebra as an element of the native central-simple-algebra type. -/
def scalar : CSA.{u, u} K where
  toAlgCat := AlgCat.of K K

variable {K}

/-- The one-by-one matrix equivalence using the canonical `Fin 1` instances. -/
def finOneMatrixAlgEquiv (A : Type*) [Ring A] [Algebra K A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[K] A where
  __ := Matrix.uniqueLinearEquiv (m := Fin 1) (n := Fin 1) (R := K) (A := A)
  map_mul' M N := by simp [Matrix.mul_apply]
  commutes' k := by simp [Matrix.algebraMap_matrix_apply]

/-- An actual matrix splitting identifies the algebra with the scalar Brauer class. -/
theorem isBrauerEquivalent_scalar_of_matrix (A : CSA.{u, u} K)
    (n : ℕ) [NeZero n] (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    IsBrauerEquivalent A (scalar K) := by
  exact ⟨1, n, one_ne_zero, NeZero.ne n,
    ⟨(finOneMatrixAlgEquiv A).trans e⟩⟩

/-- A matrix splitting computes the dimension as the square of its size. -/
theorem finrank_eq_sq_of_matrix (A : CSA K) (n : ℕ)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) : Module.finrank K A = n ^ 2 := by
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
  simp [pow_two]

/-- In a specified splitting, vanishing of the actual determinant detects nonunits. -/
theorem det_eq_zero_iff_not_isUnit_of_matrix (A : CSA K) (n : ℕ)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) (a : A) :
    (e a).det = 0 ↔ ¬ IsUnit a := by
  rw [← MulEquiv.isUnit_map e, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact not_not.symm

/-- Every central simple algebra over an algebraically closed field has scalar Brauer class. -/
theorem isBrauerEquivalent_scalar_of_isAlgClosed [IsAlgClosed K] (A : CSA.{u, u} K) :
    IsBrauerEquivalent A (scalar K) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K A
  exact isBrauerEquivalent_scalar_of_matrix A n e

/-- Actual algebraically closed splitting includes the positive matrix size and square dimension. -/
theorem exists_matrix_finrank_sq_of_isAlgClosed [IsAlgClosed K] (A : CSA K) :
    ∃ (n : ℕ), 0 < n ∧ Module.finrank K A = n ^ 2 ∧
      Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K A
  exact ⟨n, Nat.pos_of_ne_zero (NeZero.ne n), finrank_eq_sq_of_matrix A n e, ⟨e⟩⟩

end CSA

namespace BrauerGroup

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- The existing Brauer quotient over an algebraically closed field is a singleton.
This does not presume a group law on that quotient. -/
theorem subsingleton_of_isAlgClosed : Subsingleton (BrauerGroup.{u, u} K) := by
  refine ⟨?_⟩
  intro a b
  induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
      exact Quotient.sound ((CSA.isBrauerEquivalent_scalar_of_isAlgClosed A).trans
        (CSA.isBrauerEquivalent_scalar_of_isAlgClosed B).symm)

end BrauerGroup
