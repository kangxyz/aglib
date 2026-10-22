/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Lifting a residual row relation to an invertible row replacement

A nonzero relation over the residue field has a unit pivot after lifting its
coefficients. Replacing that row of the identity gives an actual unit matrix.
The associated change of generators preserves the relation ideal and its points.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {R : Type*} [CommRing R]
variable {n m : Type*} [Fintype n] [DecidableEq n]

/-- Replacing one row of the identity by a vector has determinant its pivot entry. -/
theorem det_one_updateRow (i : n) (a : n → R) :
    ((1 : Matrix n n R).updateRow i a).det = a i := by
  have ha : (∑ k, a k • (1 : Matrix n n R) k) = a := by
    funext j
    simp [Matrix.one_apply]
  simpa only [ha, Matrix.det_one, smul_eq_mul, mul_one] using
    Matrix.det_updateRow_sum (1 : Matrix n n R) i a

/-- A unit pivot makes the corresponding identity-row replacement invertible. -/
theorem isUnit_one_updateRow (i : n) (a : n → R) (hi : IsUnit (a i)) :
    IsUnit ((1 : Matrix n n R).updateRow i a) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simpa only [det_one_updateRow] using hi

/-- Lift a specified nonzero residual row relation. The resulting actual row
replacement is invertible and sends its pivot row into the maximal ideal. -/
theorem exists_unit_rowReplacement_of_residue_relation [IsLocalRing R]
    (M : Matrix n m R) (c : n → IsLocalRing.ResidueField R) (hc : c ≠ 0)
    (hrel : ∀ j, ∑ k, c k * IsLocalRing.residue R (M k j) = 0) :
    ∃ (a : n → R) (i : n),
      (∀ k, IsLocalRing.residue R (a k) = c k) ∧ IsUnit (a i) ∧
      ((1 : Matrix n n R).updateRow i a).det = a i ∧
      IsUnit ((1 : Matrix n n R).updateRow i a) ∧
      ∀ j, (((1 : Matrix n n R).updateRow i a) * M) i j ∈
        IsLocalRing.maximalIdeal R := by
  classical
  choose a ha using fun k => IsLocalRing.residue_surjective (R := R) (c k)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  have hu : IsUnit (a i) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by
    simpa only [ha, Pi.zero_apply] using hi)
  refine ⟨a, i, ha, hu, det_one_updateRow i a, isUnit_one_updateRow i a hu, ?_⟩
  intro j
  rw [Matrix.updateRow_mul, Matrix.one_mul, Matrix.updateRow_self]
  apply (IsLocalRing.residue_eq_zero_iff _).mp
  change IsLocalRing.residue R (∑ k, a k * M k j) = 0
  simpa only [map_sum, map_mul, ha] using hrel j

end Matrix

namespace Ideal

variable {S T : Type*} [CommRing S] [CommRing T]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Every matrix combination of a finite family belongs to its generated ideal. -/
theorem span_range_mulVec_le (U : Matrix n n S) (F : n → S) :
    span (Set.range (U *ᵥ F)) ≤ span (Set.range F) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (∑ j, U i j * F j) ∈ span (Set.range F)
  apply (span (Set.range F)).sum_mem
  intro j _hj
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- An invertible matrix changes generators without changing their actual ideal. -/
theorem span_range_mulVec_of_isUnit (U : Matrix n n S) (hU : IsUnit U) (F : n → S) :
    span (Set.range (U *ᵥ F)) = span (Set.range F) := by
  apply le_antisymm (span_range_mulVec_le U F)
  obtain ⟨u, rfl⟩ := hU
  simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using
    span_range_mulVec_le (↑u⁻¹ : Matrix n n S) ((u : Matrix n n S) *ᵥ F)

/-- An invertible change of equations preserves points under every ring map. -/
theorem map_mulVec_eq_zero_iff_of_isUnit
    (U : Matrix n n S) (hU : IsUnit U) (F : n → S) (φ : S →+* T) :
    (∀ i, φ ((U *ᵥ F) i) = 0) ↔ ∀ i, φ (F i) = 0 := by
  have hker (G : n → S) :
      span (Set.range G) ≤ RingHom.ker φ ↔ ∀ i, φ (G i) = 0 := by
    rw [Ideal.span_le]
    constructor
    · intro h i
      exact h ⟨i, rfl⟩
    · intro h x hx
      obtain ⟨i, rfl⟩ := hx
      exact h i
  rw [← hker (U *ᵥ F), span_range_mulVec_of_isUnit U hU F, hker F]

end Ideal
