/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Coefficients of a product of binary linear forms

Coordinate `k` is the coefficient of `T^(n-k) U^k` in
`∏ i, (x i * T + y i * U)`, computed after dehomogenizing `U = 1`.
The coefficient order is the original Stacks 0A4F order: the first
coordinate is `∏ i, x i`, and the last is `∏ i, y i`.

-/

@[expose] public noncomputable section

open scoped BigOperators
open Polynomial

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The original binary linear form in the chart `U = 1`. -/
def linear (x y : R) : R[X] := Polynomial.C x * Polynomial.X + Polynomial.C y

/-- The polynomial obtained from the original product of binary linear forms. -/
def polynomial (x y : Fin n → R) : R[X] := ∏ i, linear (x i) (y i)

/-- The coefficient in the original descending-degree binary-form order. -/
def coefficient (x y : Fin n → R) (k : Fin (n + 1)) : R :=
  (polynomial x y).coeff (n - k.val)

@[simp]
theorem linear_coeff_zero (x y : R) : (linear x y).coeff 0 = y := by
  simp [linear]

@[simp]
theorem linear_coeff_one (x y : R) : (linear x y).coeff 1 = x := by
  simp [linear]

theorem linear_eq_zero_iff (x y : R) : linear x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · simpa using congrArg (fun p : R[X] => p.coeff 1) h
    · simpa using congrArg (fun p : R[X] => p.coeff 0) h
  · rintro ⟨rfl, rfl⟩
    simp [linear]

theorem natDegree_linear_le (x y : R) : (linear x y).natDegree ≤ 1 :=
  Polynomial.natDegree_linear_le

theorem natDegree_polynomial_le (x y : Fin n → R) : (polynomial x y).natDegree ≤ n := by
  calc
    (polynomial x y).natDegree ≤ ∑ i : Fin n, (linear (x i) (y i)).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ (fun i => linear (x i) (y i))
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => natDegree_linear_le _ _)
    _ = n := by simp

@[simp]
theorem coefficient_first (x y : Fin n → R) : coefficient x y 0 = ∏ i, x i := by
  have h := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ)
    (fun i : Fin n => linear (x i) (y i)) 1 (fun i _ => natDegree_linear_le _ _)
  simpa only [coefficient, Fin.val_zero, Nat.sub_zero, polynomial, Finset.card_univ,
    Fintype.card_fin, mul_one, linear_coeff_one] using h

@[simp]
theorem coefficient_last (x y : Fin n → R) :
    coefficient x y (Fin.last n) = ∏ i, y i := by
  simpa only [coefficient, Fin.val_last, Nat.sub_self, polynomial, linear_coeff_zero] using
    (Polynomial.coeff_zero_prod (s := Finset.univ) (fun i : Fin n => linear (x i) (y i)))

@[simp]
theorem polynomial_zero (x y : Fin 0 → R) : polynomial x y = 1 := by
  simp [polynomial]

@[simp]
theorem coefficient_zero_factors (x y : Fin 0 → R) (k : Fin 1) : coefficient x y k = 1 := by
  have hk : k = 0 := Fin.eq_zero k
  subst k
  simp [coefficient]

theorem polynomial_succ (x y : Fin (n + 1) → R) :
    polynomial x y = linear (x 0) (y 0) *
      polynomial (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ) := by
  simp [polynomial, Fin.prod_univ_succ]

theorem polynomial_map {S : Type v} [CommRing S] (σ : R →+* S) (x y : Fin n → R) :
    (polynomial x y).map σ = polynomial (fun i => σ (x i)) (fun i => σ (y i)) := by
  rw [polynomial, Polynomial.map_prod]
  simp only [polynomial, linear, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X]

/-- The same original coefficient polynomials commute with every coefficient ring map. -/
theorem coefficient_map {S : Type v} [CommRing S] (σ : R →+* S)
    (x y : Fin n → R) (k : Fin (n + 1)) :
    coefficient (fun i => σ (x i)) (fun i => σ (y i)) k = σ (coefficient x y k) := by
  simpa only [coefficient, Polynomial.coeff_map] using
    (congrArg (fun p : S[X] => p.coeff (n - k.val)) (polynomial_map σ x y)).symm

theorem linear_scale (u x y : R) : linear (u * x) (u * y) = Polynomial.C u * linear x y := by
  simp [linear, map_mul, mul_add, mul_assoc]

theorem polynomial_scale (u x y : Fin n → R) :
    polynomial (fun i => u i * x i) (fun i => u i * y i) =
      Polynomial.C (∏ i, u i) * polynomial x y := by
  simp [polynomial, linear_scale, Finset.prod_mul_distrib]

/-- Rescaling each original pair rescales every output coordinate by the same product. -/
theorem coefficient_scale (u x y : Fin n → R) (k : Fin (n + 1)) :
    coefficient (fun i => u i * x i) (fun i => u i * y i) k =
      (∏ i, u i) * coefficient x y k := by
  simpa only [coefficient, Polynomial.coeff_C_mul] using
    congrArg (fun p : R[X] => p.coeff (n - k.val)) (polynomial_scale u x y)

theorem polynomial_reindex (e : Equiv.Perm (Fin n)) (x y : Fin n → R) :
    polynomial (fun i => x (e i)) (fun i => y (e i)) = polynomial x y := by
  exact Equiv.prod_comp e (fun i => linear (x i) (y i))

theorem coefficient_reindex (e : Equiv.Perm (Fin n))
    (x y : Fin n → R) (k : Fin (n + 1)) :
    coefficient (fun i => x (e i)) (fun i => y (e i)) k = coefficient x y k :=
  congrArg (fun p : R[X] => p.coeff (n - k.val)) (polynomial_reindex e x y)

/-- A generating original pair gives a primitive linear polynomial over every ring. -/
theorem contentIdeal_linear_eq_top (x y : R) (h : Ideal.span ({x, y} : Set R) = ⊤) :
    (linear x y).contentIdeal = ⊤ := by
  apply top_unique
  rw [← h]
  apply Ideal.span_le.mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz
  · rw [hz]
    change x ∈ (linear x y).contentIdeal
    have hx := (linear x y).coeff_mem_contentIdeal 1
    rw [linear_coeff_one] at hx
    exact hx
  · rw [hz]
    change y ∈ (linear x y).contentIdeal
    have hy := (linear x y).coeff_mem_contentIdeal 0
    rw [linear_coeff_zero] at hy
    exact hy

/-- The original product remains primitive, including for nonreduced rings
and for the empty product. -/
theorem contentIdeal_polynomial_eq_top (x y : Fin n → R)
    (h : ∀ i, Ideal.span ({x i, y i} : Set R) = ⊤) :
    (polynomial x y).contentIdeal = ⊤ := by
  classical
  have hs (s : Finset (Fin n)) : (∏ i ∈ s, linear (x i) (y i)).contentIdeal = ⊤ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact Polynomial.contentIdeal_mul_eq_top_of_contentIdeal_eq_top
        (contentIdeal_linear_eq_top (x i) (y i) (h i)) ih
  exact hs Finset.univ

/-- The displayed `n+1` output coordinates generate the entire original content ideal. -/
theorem span_coefficients_eq_contentIdeal (x y : Fin n → R) :
    Ideal.span (Set.range (coefficient x y)) = (polynomial x y).contentIdeal := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact (polynomial x y).coeff_mem_contentIdeal (n - k.val)
  · rw [Polynomial.contentIdeal_def]
    apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Polynomial.mem_coeffs_iff.mp hr
    have hjn : j ≤ n :=
      (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans
        (natDegree_polynomial_le x y)
    refine Ideal.subset_span ⟨⟨n - j, Nat.lt_succ_of_le (Nat.sub_le n j)⟩, ?_⟩
    simp only [coefficient, Nat.sub_sub_self hjn]

/-- The binary-form coefficient family has no common zero whenever each
original pair generates the unit ideal. No factorial is inverted. -/
theorem span_coefficients_eq_top (x y : Fin n → R)
    (h : ∀ i, Ideal.span ({x i, y i} : Set R) = ⊤) :
    Ideal.span (Set.range (coefficient x y)) = ⊤ := by
  rw [span_coefficients_eq_contentIdeal, contentIdeal_polynomial_eq_top x y h]

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
