/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure

/-!
# Projective space as a scheme over `Spec R`

For `R : CommRingCat`, `schemeOver R ι` is `ProjectiveSpace R ι` with its structure morphism
`toSpec R ι`, as an object of `Over (Spec R)`. It is the projective-space counterpart of
`Grassmannian.schemeOver`, and its consumer is the comparison with the Grassmannian of rank-one
quotients (`Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : CommRingCat.{u}) (ι : Type u)

/-- Projective space as a scheme over `Spec R`, by its structure morphism `toSpec R ι`. -/
abbrev schemeOver : Over (Spec R) := Over.mk (toSpec R ι)

end AlgebraicGeometry.ProjectiveSpace
