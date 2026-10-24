/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Mathlib.Algebra.BigOperators.Fin

/-! # Finite ordered tensor products of actual line bundles

The factors may vary. The empty tensor is the existing trivial line bundle,
and its original Picard class is the sum of the original factor classes.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable (X : Scheme.{u})

/-- The ordered tensor of a finite tuple of actual line bundles, with trivial
empty tensor. Unlike a tensor power, its factors need not coincide. -/
def finiteTensorLineBundle : {n : ℕ} → (Fin n → LineBundle X) → LineBundle X
  | 0, _ => trivialLineBundle X
  | n + 1, L => tensorLineBundle X (L 0)
      (finiteTensorLineBundle (fun i : Fin n => L i.succ))

/-- The original Picard class of the actual finite tensor is the sum of the
original factor classes, including the empty tuple. -/
@[simp] theorem classOf_finiteTensor {n : ℕ} (L : Fin n → LineBundle X) :
    classOf X (finiteTensorLineBundle X L) = ∑ i, classOf X (L i) := by
  induction n with
  | zero => simp [finiteTensorLineBundle]
  | succ n ih =>
    rw [finiteTensorLineBundle, classOf_tensor, ih, Fin.sum_univ_succ]

end AlgebraicGeometry.Scheme.Modules.Invertible
