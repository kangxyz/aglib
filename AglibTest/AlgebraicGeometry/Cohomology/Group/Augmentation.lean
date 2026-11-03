/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Augmentation

/-! The augmentation uses the original scalar action and grading
projection on the actual cohomology direct sum. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

variable {k : Type u} [Field k] (X : FScheme k)
  [IsProper X.hom] [GeometricallyIntegral X.hom]

example (a : k) :
    structureCohomologyAugmentation X (algebraMap k (structureCohomologyAlgebra X) a) = a :=
  (structureCohomologyAugmentation X).commutes a

example (x : structureCohomologyAlgebra X) :
    GradedAlgebra.proj (structureCohomologyGrade X) 0 x =
      structureCohomologyAugmentation X x • (1 : structureCohomologyAlgebra X) :=
  structureCohomology_proj_zero X x
