/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.PowerBasis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Minimal polynomials under literal scalar extension

For an integral element of an arbitrary algebra over a field, the minimal
polynomial of `1 ⊗ a` is the coefficient extension of the original minimal
polynomial. This is stronger than merely having a divisibility: scalar
extension preserves linear independence of the initial powers. The algebra
need not be commutative or remain a domain after extension.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Polynomial

namespace Algebra

variable {K L A : Type*} [Field K] [Field L] [Ring A]
  [Algebra K L] [Algebra K A]

/-- Literal scalar extension does not lower the minimal-polynomial degree of
an integral element, even when the extended algebra has zero divisors. -/
theorem minpoly_one_tmul (a : A) (ha : IsIntegral K a) :
    minpoly L (1 ⊗ₜ[K] a : L ⊗[K] A) = (minpoly K a).map (algebraMap K L) := by
  let j : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight
  have hcomp : (algebraMap L (L ⊗[K] A)).comp (algebraMap K L) =
      j.toRingHom.comp (algebraMap K A) := by
    ext k
    simp
  have hz : aeval (1 ⊗ₜ[K] a : L ⊗[K] A)
      ((minpoly K a).map (algebraMap K L)) = 0 := by
    have h := Polynomial.map_aeval_eq_aeval_map hcomp (minpoly K a) a
    rw [minpoly.aeval, map_zero] at h
    exact h.symm
  apply minpoly.eq_of_linearIndependent L (1 ⊗ₜ[K] a : L ⊗[K] A)
    ((minpoly.monic ha).map _) hz
    (minpoly K a).natDegree
  · rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (minpoly.ne_zero ha)]
  · simpa only [Algebra.TensorProduct.tmul_pow, one_pow] using
      Module.Flat.linearIndependent_one_tmul (S := L) (linearIndependent_pow a)

/-- In particular the degree is unchanged by scalar extension. -/
theorem natDegree_minpoly_one_tmul (a : A) (ha : IsIntegral K a) :
    (minpoly L (1 ⊗ₜ[K] a : L ⊗[K] A)).natDegree = (minpoly K a).natDegree := by
  rw [minpoly_one_tmul a ha, Polynomial.natDegree_map]

end Algebra
