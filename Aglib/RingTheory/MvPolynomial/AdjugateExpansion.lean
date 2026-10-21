/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.ScaledTaylor
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Tactic.Ring

/-!
# Adjugate-scaled polynomial expansion

For a square polynomial system, the adjugate change of variables extracts
the square of the evaluated Jacobian determinant and leaves a quadratic
remainder. No determinant cancellation, domain, or invertibility hypothesis
is used. Finite empty index types are permitted.

The local matrix in the statement has equations in rows and variables in
columns. This is the transpose of the native pre-submersive presentation's
`jacobiMatrix` convention when their coordinates agree. No additional
Jacobian object or instance is introduced. This purely algebraic expansion
is not a Hensel lifting or Artin approximation theorem.
-/

@[expose] public section

open scoped Matrix

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- The adjugate-scaled change of variables extracts the determinant squared
without cancellation. The displayed Jacobian has equations in rows. -/
theorem exists_adjugate_scaled_remainder
    (F : σ → MvPolynomial σ R) (y : σ → R) :
    let J : Matrix σ σ R := fun i j ↦ eval y (pderiv j (F i))
    let z : σ → MvPolynomial σ R := J.adjugate.map C *ᵥ X
    ∃ Q : σ → MvPolynomial σ R, ∀ i,
      Q i ∈ idealOfVars σ R ^ 2 ∧
      aeval (fun j ↦ C (y j) + C J.det * z j) (F i) =
        C (eval y (F i)) + C (J.det ^ 2) * (X i + Q i) := by
  classical
  dsimp only
  let J : Matrix σ σ R := fun i j ↦ eval y (pderiv j (F i))
  let z : σ → MvPolynomial σ R := J.adjugate.map C *ᵥ X
  have hz (j : σ) : z j ∈ idealOfVars σ R := by
    apply Ideal.sum_mem
    intro k _
    exact (idealOfVars σ R).mul_mem_left _
      (Ideal.subset_span (Set.mem_range_self k))
  have hmatrix : J.map C * J.adjugate.map C =
      (C J.det : MvPolynomial σ R) • (1 : Matrix σ σ (MvPolynomial σ R)) := by
    rw [← Matrix.map_mul, Matrix.mul_adjugate]
    apply Matrix.ext
    intro i j
    by_cases h : i = j <;> simp [h]
  have hvec : J.map C *ᵥ z = (C J.det : MvPolynomial σ R) • (X : σ → MvPolynomial σ R) := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, hmatrix, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hlinear (i : σ) :
      (∑ j, C (eval y (pderiv j (F i))) * z j) = C J.det * X i := by
    change ((J.map C) *ᵥ z) i =
      ((C J.det : MvPolynomial σ R) • (X : σ → MvPolynomial σ R)) i
    exact congrFun hvec i
  have hex (i : σ) := exists_scaled_firstOrder_remainder
    (F i) y J.det z (idealOfVars σ R) hz
  choose Q hQ hE using hex
  refine ⟨Q, fun i ↦ ⟨hQ i, ?_⟩⟩
  have hi := hE i
  change aeval (fun j ↦ C (y j) + C J.det * z j) (F i) =
    C (eval y (F i)) + C J.det *
      (∑ j, C (eval y (pderiv j (F i))) * z j) + C (J.det ^ 2) * Q i at hi
  rw [hi, hlinear, map_pow]
  ring

end MvPolynomial
