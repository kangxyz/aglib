/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Basic

/-!
# Evaluation as the norm in a whole monic polynomial algebra

The characteristic polynomial of multiplication by the original root is the
original monic polynomial. Thus the determinant norm of a scalar minus that
root is evaluation, even when the algebra is reducible or nonreduced.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k : Type*} [Field k]

/-- The norm in the entire monic quotient algebra is the original polynomial
evaluation; no choice of root field, irreducibility or separability is involved. -/
theorem norm_algebraMap_sub_root (p : k[X]) (hp : p.Monic) (a : k) :
    Algebra.norm k (algebraMap k (AdjoinRoot p) a - root p) = p.eval a := by
  let pb := powerBasis hp.ne_zero
  have hm : minpoly k pb.gen = p := minpoly_powerBasis_gen_of_monic hp
  have hc := charpoly_leftMulMatrix pb
  rw [hm] at hc
  rw [Algebra.norm_eq_matrix_det pb.basis, map_sub]
  have ha : Algebra.leftMulMatrix pb.basis (algebraMap k (AdjoinRoot p) a) =
      Matrix.scalar (Fin pb.dim) a := by
    exact (Algebra.leftMulMatrix pb.basis).commutes a
  rw [ha]
  change (Matrix.scalar (Fin pb.dim) a - Algebra.leftMulMatrix pb.basis pb.gen).det = _
  rw [← Matrix.eval_charpoly, hc]

/-- In particular the complement of the original root has norm `p(1)`,
including all branch degrees and nonreduced multiplicities. -/
theorem norm_one_sub_root (p : k[X]) (hp : p.Monic) :
    Algebra.norm k (1 - root p) = p.eval 1 := by
  simpa only [map_one] using norm_algebraMap_sub_root p hp 1

end AdjoinRoot
