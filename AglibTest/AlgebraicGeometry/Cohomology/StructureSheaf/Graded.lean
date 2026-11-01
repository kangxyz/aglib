/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Graded

/-! Consumers use the native direct-sum ring and the original component
maps, without a selected replacement for a cohomology group. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

@[expose] public noncomputable section

variable {k : Type u} [Field k] (X : FScheme k)

example : Ring (structureCohomologyAlgebra X) := inferInstance

example : Algebra k (structureCohomologyAlgebra X) := inferInstance

example (a : k) :
    algebraMap k (structureCohomologyAlgebra X) a =
      structureCohomologyInclusion X 0 (a • structureCupUnit X) := rfl

example (n : ℕ) (x : structureCohomologyAlgebra X) :
    GradedAlgebra.proj (structureCohomologyGrade X) n x =
      structureCohomologyInclusion X n (structureCohomologyComponent X n x) :=
  structureCohomology_proj X n x
