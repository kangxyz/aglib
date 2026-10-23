/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.FieldAlgebra

/-!
# Recovering the original descending-degree coefficient vector

The polynomial formed from an arbitrary `n+1`-tuple retains that same tuple
in the original Stacks coefficient order. Over an algebraically closed field,
every nonzero tuple is a nonzero scalar multiple of coefficients of exactly
`n` normalized original factor pairs.
-/

@[expose] public noncomputable section

open scoped BigOperators
open Polynomial

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The polynomial with the given original descending-degree coefficient vector. -/
def ofCoefficients (a : Fin (n + 1) → R) : R[X] :=
  ∑ j, Polynomial.monomial (n - j.val) (a j)

@[simp]
theorem ofCoefficients_coeff (a : Fin (n + 1) → R) (k : Fin (n + 1)) :
    (ofCoefficients a).coeff (n - k.val) = a k := by
  classical
  rw [ofCoefficients, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · exact Polynomial.coeff_monomial_same _ _
  · intro j _ hjk
    rw [Polynomial.coeff_monomial, ite_eq_right]
    intro h
    apply hjk
    apply Fin.ext
    have hj := j.isLt
    have hk := k.isLt
    omega
  · simp

theorem natDegree_ofCoefficients_le (a : Fin (n + 1) → R) :
    (ofCoefficients a).natDegree ≤ n := by
  unfold ofCoefficients
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le (a j)).trans (Nat.sub_le n j.val)

theorem ofCoefficients_ne_zero (a : Fin (n + 1) → R) (ha : ∃ j, a j ≠ 0) :
    ofCoefficients a ≠ 0 := by
  obtain ⟨j, hj⟩ := ha
  intro h
  apply hj
  have hc := congrArg (fun p : R[X] => p.coeff (n - j.val)) h
  simpa only [ofCoefficients_coeff, Polynomial.coeff_zero] using hc

theorem ofCoefficients_coefficient (x y : Fin n → R) :
    ofCoefficients (coefficient x y) = polynomial x y := by
  apply (Polynomial.ext_iff_natDegree_le (natDegree_ofCoefficients_le _)
    (natDegree_polynomial_le x y)).mpr
  intro m hm
  let k : Fin (n + 1) := ⟨n - m, Nat.lt_succ_of_le (Nat.sub_le n m)⟩
  have hk : n - k.val = m := Nat.sub_sub_self hm
  rw [← hk, ofCoefficients_coeff]
  rfl

namespace Field

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Every nonzero original projective coefficient vector is a scalar multiple
of the coefficients of exactly `n` original normalized pairs, including infinity. -/
theorem exists_coefficient_factorization (v : Fin (n + 1) → K) (hv : ∃ j, v j ≠ 0) :
    ∃ (a : Fin n → Option K) (c : K), c ≠ 0 ∧
      ∀ j, v j = c * coefficient (fun i => first (a i)) (fun i => second (a i)) j := by
  obtain ⟨a, c, hc, ha⟩ := exists_normalized_factorization (ofCoefficients v)
    (ofCoefficients_ne_zero v hv) (natDegree_ofCoefficients_le v)
  refine ⟨a, c, hc, fun j => ?_⟩
  have h := congrArg (fun p : K[X] => p.coeff (n - j.val)) ha
  simpa only [ofCoefficients_coeff, Polynomial.coeff_C_mul, normalizedPolynomial,
    coefficient] using h

end Field

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
