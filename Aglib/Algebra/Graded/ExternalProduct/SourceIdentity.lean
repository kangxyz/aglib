/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.ExternalProduct

/-!
# Identity of the selected graded tensor source

The original direct-sum source equivalence is Mathlib's graded tensor
equivalence for the same supplied homogeneous submodules and grade instances.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u m n

namespace DirectSum

variable {R : Type u} [CommRing R]
  {M : ℕ → Type m} {N : ℕ → Type n}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [GRing M] [GAlgebra R M] [GRing N] [GAlgebra R N]
  [gradeM : GradedAlgebra (summandSubmodule (R := R) M)]
  [gradeN : GradedAlgebra (summandSubmodule (R := R) N)]

/-- The chosen original tensor source is the same whole graded tensor map. -/
theorem externalProductSourceEquiv_eq_of :
    externalProductSourceEquiv (R := R) (M := M) (N := N)
        (gradeM := gradeM) (gradeN := gradeN) =
      GradedTensorProduct.of R (summandSubmodule (R := R) M)
        (summandSubmodule (R := R) N) := rfl

end DirectSum
