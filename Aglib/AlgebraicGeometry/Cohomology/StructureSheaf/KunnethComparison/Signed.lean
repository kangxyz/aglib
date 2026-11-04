/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct.SignedComparison
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.HomogeneousValues
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Graded.Basic

/-!
# The original signed forward map is the original total Kunneth operator

The original source and signed value laws are compared with the independently
proved total-map values. The original graded data and source equivalence are retained.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

set_option maxHeartbeats 1000000 in
-- Retain the original finite local allowance for this same native signed equality.
/-- The literal original signed external map is the original total Kunneth operator. -/
theorem structureExternalLinearMap_signed :
    DirectSum.ExternalSignedTotalEq
      (gradeM := structureCohomologyGradedAlgebra X)
      (gradeN := structureCohomologyGradedAlgebra Y)
      (structureExternalAlgebraMap X Y) (structureExternalTensorSourceEquiv X Y)
      (structureExternalLinearMap X Y) := by
  refine DirectSum.externalSignedTotalEq_of_values
    (structureExternalAlgebraMap X Y) (structureExternalTensorSourceEquiv X Y)
    (structureExternalLinearMap X Y)
    (fun p q x y => structureExternalCup X Y (p := p) (q := q) rfl x y) ?_ ?_ ?_
  · exact structureExternalTensorSourceEquiv_tmul X Y
  · intro p q x y
    exact structureExternalAlgebraMap_tmul X Y rfl x y
  · intro p q x y
    exact structureExternalLinearMap_tmul X Y rfl x y

end AlgebraicGeometry.Scheme.Cohomology
