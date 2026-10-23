/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.MinimalPolynomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Separability and degree detected in a splitting

A separable characteristic polynomial in a matrix splitting forces the original
minimal polynomial to be separable and to have the matrix size as its degree.
This is the algebraic step after choosing a generic separable element; the
existence of such an element is not assumed to hold automatically here.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Polynomial

namespace Algebra

private theorem minpoly_eq_charpoly_of_separable {L : Type*} [Field L]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) L)
    (hs : M.charpoly.Separable) (hsp : M.charpoly.Splits) :
    minpoly L M = M.charpoly := by
  have hr : M.charpoly.roots ≤ (minpoly L M).roots := by
    apply (Multiset.le_iff_subset (Polynomial.nodup_roots hs)).mpr
    intro x hx
    apply (Polynomial.mem_roots (minpoly.ne_zero M.isIntegral)).mpr
    have he : Module.End.HasEigenvalue M.toLin' x :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly M.toLin' x).mpr
        (by simpa only [Matrix.charpoly_toLin'] using Polynomial.isRoot_of_mem_roots hx)
    simpa only [Matrix.minpoly_toLin'] using
      (Module.End.hasEigenvalue_iff_isRoot (f := M.toLin') (μ := x)).mp he
  have hd := hsp.dvd_of_roots_le_roots M.charpoly_monic.ne_zero hr
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le M.charpoly_monic
    (minpoly.monic M.isIntegral) hd
    (Polynomial.natDegree_le_of_dvd M.minpoly_dvd_charpoly M.charpoly_monic.ne_zero)

/-- An element whose matrix characteristic polynomial is separable in an
algebraically closed splitting generates a separable algebra of full matrix degree. -/
theorem separable_minpoly_and_natDegree_of_splitting
    {K L A : Type*} [Field K] [Field L] [IsAlgClosed L] [Ring A]
    [Algebra K L] [Algebra K A] {n : ℕ}
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (a : A) (ha : IsIntegral K a)
    (hs : (e (1 ⊗ₜ[K] a)).charpoly.Separable) :
    (minpoly K a).Separable ∧ (minpoly K a).natDegree = n := by
  have heq : (minpoly K a).map (algebraMap K L) =
      (e (1 ⊗ₜ[K] a)).charpoly := by
    rw [← minpoly_one_tmul a ha, ← minpoly.algEquiv_eq e]
    exact minpoly_eq_charpoly_of_separable _ hs (IsAlgClosed.splits _)
  constructor
  · apply (Polynomial.separable_map (algebraMap K L)).mp
    rwa [heq]
  · have h := congrArg Polynomial.natDegree heq
    simpa only [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin] using h

end Algebra
