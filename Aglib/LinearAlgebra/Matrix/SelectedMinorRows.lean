/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Matrix.MinorIdealValuation

/-! # An actual selected row matrix retains the full minor ideal

This supplies the exact full-row minor ideal required by normalized retained
adjugate minors, starting from the original evaluated relation matrix.
-/

@[expose] public section

namespace Matrix

/-- Selecting the rows of a minimum-order minor preserves the full minor ideal. -/
theorem exists_selected_rows_minorIdeal_eq
    {R m n : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : Matrix m n R) (r : ℕ) (h : A.minorIdeal r ≠ ⊥) :
    ∃ (rows : Fin r → m) (cols : Fin r → n) (δ : R),
      δ ≠ 0 ∧ (A.submatrix rows cols).det = δ ∧
      (A.submatrix rows _root_.id).minorIdeal r = Ideal.span {δ} ∧
      Ideal.span {δ} = A.minorIdeal r := by
  obtain ⟨rows, cols, hne, hspan⟩ := A.exists_minor_span_singleton_eq r h
  refine ⟨rows, cols, (A.submatrix rows cols).det, hne, rfl, ?_, hspan⟩
  apply le_antisymm
  · rw [hspan]
    apply Ideal.span_le.mpr
    rintro x ⟨a, b, hx⟩
    exact Ideal.subset_span ⟨rows ∘ a, b, hx⟩
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.subset_span ⟨_root_.id, cols, rfl⟩

end Matrix
