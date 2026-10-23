/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Matrix

/-!
# Centrality descends from a nonempty matrix algebra

The scalar-matrix embedding and its diagonal entries recover centrality of the
coefficient algebra. The nonempty index hypothesis is essential.
-/

@[expose] public section

namespace Algebra.IsCentral

variable (K D ι : Type*) [CommSemiring K] [Semiring D] [Algebra K D]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- If a nonempty finite matrix algebra is central, its coefficient algebra is central. -/
theorem of_matrix [IsCentral K (Matrix ι ι D)] : IsCentral K D where
  out x hx := by
    have hxc : Matrix.scalarAlgHom ι K x ∈ Subalgebra.center K (Matrix ι ι D) := by
      rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
      exact ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := IsCentral.out hxc
    refine ⟨k, ?_⟩
    let i : ι := Classical.choice ‹Nonempty ι›
    simpa [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply] using
      congrArg (fun M : Matrix ι ι D => M i i) hk

end Algebra.IsCentral
