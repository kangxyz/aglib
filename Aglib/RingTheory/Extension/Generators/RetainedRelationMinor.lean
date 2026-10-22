/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Generators.LinearChangeDerivative
public import Mathlib.RingTheory.Ideal.Span

/-! # Retaining an actual relation minor under the same coordinate change

Literal inverse substitution produces relations in the genuinely changed presentation.
The normalized adjugate determinant of that same matrix then supplies a retained
Jacobian minor generating the required principal ideal after evaluation.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped Matrix

namespace Algebra.Generators

variable {R B S n : Type*} [CommRing R] [CommRing B] [CommRing S]
  [Algebra R B] [Algebra R S] [Fintype n] [DecidableEq n]
variable (P : Generators R B n) (U : Matrix n n R) (hU : IsUnit U.det)
  (χ : B →ₐ[R] S)

/-- The evaluated relation-row Jacobian transforms by the inverse of the same matrix. -/
theorem evaluatedJacobian_inverseLinearSubstitution {m : Type*}
    (f : m → MvPolynomial n R) :
    (Matrix.of fun i j => χ (aeval (P.linearChange U hU).val
      (pderiv j (inverseLinearSubstitution U (f i))))) =
      (Matrix.of fun i j => χ (aeval P.val (pderiv j (f i)))) *
        (algebraMap R S).mapMatrix U⁻¹ := by
  apply Matrix.ext
  intro i j
  change χ (aeval (P.linearChange U hU).val
    (pderiv j (inverseLinearSubstitution U (f i)))) = _
  rw [aeval_pderiv_inverseLinearSubstitution]
  simp only [map_sum, map_mul, χ.commutes, Matrix.mul_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

/-- Actual transformed relations and their retained minor are produced from the
same matrix and its normalized adjugate determinant. The normalization is an
intermediate output of the generic-coordinate construction, not a new matrix choice. -/
theorem retained_relation_minor {c : ℕ} (f : Fin c → P.ker) (b : Fin c ↪ n)
    (δ h : S) (hh : IsUnit h)
    (hnorm :
      ((Matrix.of (fun i j => χ (aeval P.val (pderiv j (f i : MvPolynomial n R)))) *
        ((algebraMap R S).mapMatrix U).adjugate).submatrix _root_.id b).det = δ * h) :
    (∀ i, inverseLinearSubstitution U (f i : MvPolynomial n R) ∈
      (P.linearChange U hU).ker) ∧
    Ideal.span {(Matrix.of fun i j => χ (aeval (P.linearChange U hU).val
      (pderiv (b j) (inverseLinearSubstitution U (f i : MvPolynomial n R))))).det} =
        Ideal.span {δ} := by
  constructor
  · intro i
    exact Eq.mpr (congrArg
      (fun J : Ideal (MvPolynomial n R) => (f i : MvPolynomial n R) ∈ J)
      (P.comap_ker_inverseLinearSubstitution U hU)) (f i).property
  · let A : Matrix (Fin c) n S := fun i j =>
      χ (aeval P.val (pderiv j (f i : MvPolynomial n R)))
    let N : Matrix (Fin c) n S := fun i j =>
      χ (aeval (P.linearChange U hU).val
        (pderiv j (inverseLinearSubstitution U (f i : MvPolynomial n R))))
    let u : S := algebraMap R S (↑hU.unit⁻¹ : R)
    have hu : IsUnit u := (hU.unit⁻¹).isUnit.map (algebraMap R S)
    have hInv : (algebraMap R S).mapMatrix U⁻¹ =
        u • ((algebraMap R S).mapMatrix U).adjugate := by
      rw [Matrix.nonsing_inv_apply U hU]
      have hadj := (algebraMap R S).map_adjugate U
      apply Matrix.ext
      intro i j
      change algebraMap R S ((↑hU.unit⁻¹ : R) * U.adjugate i j) =
        u * (((algebraMap R S).mapMatrix U).adjugate i j)
      rw [map_mul]
      exact congrArg (u * ·) (congrFun (congrFun hadj i) j)
    have hN : N = u • (A * ((algebraMap R S).mapMatrix U).adjugate) := by
      have hJ := P.evaluatedJacobian_inverseLinearSubstitution U hU χ
        (fun i => (f i : MvPolynomial n R))
      change N = A * (algebraMap R S).mapMatrix U⁻¹ at hJ
      rw [hJ, hInv, Matrix.mul_smul]
    change Ideal.span {(N.submatrix _root_.id b).det} = Ideal.span {δ}
    rw [hN]
    change Ideal.span {(u • ((A * ((algebraMap R S).mapMatrix U).adjugate).submatrix
      _root_.id b)).det} = Ideal.span {δ}
    rw [Matrix.det_smul]
    change ((A * ((algebraMap R S).mapMatrix U).adjugate).submatrix _root_.id b).det = δ * h
      at hnorm
    rw [hnorm, Ideal.span_singleton_mul_left_unit (hu.pow _),
      Ideal.span_singleton_mul_right_unit hh]

end Algebra.Generators
