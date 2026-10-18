/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootNormEvaluation

/-!
# The determinant norm of the original polynomial root

For the whole algebra defined by a monic polynomial, the determinant of
multiplication by its original root is the signed constant coefficient.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k : Type*} [Field k]

/-- The ordinary determinant norm of the original root, without separability
or irreducibility assumptions. -/
theorem norm_root (p : k[X]) (hp : p.Monic) :
    Algebra.norm k (root p) = (-1) ^ p.natDegree * p.coeff 0 := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (powerBasis hp.ne_zero)
  rw [minpoly_powerBasis_gen_of_monic hp] at h
  exact h

end AdjoinRoot
