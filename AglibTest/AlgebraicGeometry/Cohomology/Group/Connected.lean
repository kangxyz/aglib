/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Connected

/-! The actual structural scalar map supplies connected degree zero
under properness and geometric integrality, in every dimension. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

@[expose] public noncomputable section

variable {k : Type u} [Field k] (X : FScheme k)
  [IsProper X.hom] [GeometricallyIntegral X.hom]

example (x : Scheme.structureCohomology k X 0) :
    (structureH0ScalarEquiv X).symm x • structureCupUnit X = x := by
  exact (structureH0ScalarEquiv X).apply_symm_apply x
