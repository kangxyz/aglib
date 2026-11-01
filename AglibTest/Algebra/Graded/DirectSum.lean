/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.DirectSum

/-! The shared internal grading retains the original direct-sum
inclusions and coordinates for an arbitrary graded module family. -/

@[expose] public noncomputable section

open scoped DirectSum

variable {ι R : Type*} [DecidableEq ι] [CommRing R]
  (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

example (i : ι) (x : M i) :
    DirectSum.homogeneousComponent (R := R) M i
      (DirectSum.homogeneousInclusion (R := R) M i x) = x :=
  DirectSum.homogeneousComponent_inclusion (R := R) M i x

example (i : ι) (x : DirectSum.summandSubmodule (R := R) M i) :
    (DirectSum.summandLinearEquiv (R := R) M i).symm x = (x : ⨁ j, M j) i :=
  DirectSum.summandLinearEquiv_symm_apply (R := R) M i x

variable [AddMonoid ι] [DirectSum.GRing M] [DirectSum.GAlgebra R M]

example (i : ι) (x : ⨁ j, M j) :
    GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) i x =
      DirectSum.lof R ι M i (x i) :=
  DirectSum.proj_summandSubmodule (R := R) M i x
