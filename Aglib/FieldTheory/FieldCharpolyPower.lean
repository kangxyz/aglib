/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Characteristic polynomial of multiplication in a finite field extension

The characteristic polynomial of actual multiplication by an element is a power
of its minimal polynomial. The exponent is the degree over its actual simple
intermediate field. The proof compares evaluations via the transitivity of norm.
-/

@[expose] public noncomputable section

namespace Algebra

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]

/-- Evaluation of the characteristic polynomial of multiplication is a norm. -/
theorem eval_charpoly_lmul (a : L) (t : k) :
    (lmul k L a).charpoly.eval t = norm k (algebraMap k L t - a) := by
  rw [LinearMap.eval_charpoly, norm_apply]
  congr 1
  ext x
  simp [Algebra.smul_def]

/-- Multiplication by the generator on its simple intermediate field has the
original element's minimal polynomial as its characteristic polynomial. -/
theorem charpoly_lmul_adjoin_gen (a : L) :
    (lmul k (IntermediateField.adjoin k {a})
      (IntermediateField.AdjoinSimple.gen k a)).charpoly = minpoly k a := by
  let b := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := k) a)
  rw [← LinearMap.charpoly_toMatrix _ b.basis]
  change (leftMulMatrix b.basis b.gen).charpoly = minpoly k a
  rw [charpoly_leftMulMatrix, IntermediateField.adjoin.powerBasis_gen,
    IntermediateField.minpoly_gen]

/-- The actual multiplication characteristic polynomial over an infinite base
field is the minimal polynomial raised to the relative extension degree. -/
theorem charpoly_lmul_eq_minpoly_pow [Infinite k] (a : L) :
    (lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L := by
  let F := IntermediateField.adjoin k {a}
  let x : F := IntermediateField.AdjoinSimple.gen k a
  have heval (t : k) :
      (lmul k L a).charpoly.eval t =
        ((minpoly k a) ^ Module.finrank F L).eval t := by
    rw [eval_charpoly_lmul, Polynomial.eval_pow]
    have hmap : algebraMap F L (algebraMap k F t - x) = algebraMap k L t - a := by
      simp [x]
    rw [← hmap, ← norm_norm (R := k) (S := F), Algebra.norm_algebraMap, map_pow]
    congr 1
    rw [← eval_charpoly_lmul, charpoly_lmul_adjoin_gen]
  exact Polynomial.funext heval

end Algebra
