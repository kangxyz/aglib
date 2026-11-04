/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Kunneth
public import Aglib.Algebra.Graded.TensorProduct.TotalValues

/-!
# The one total comparison on the original Kunneth carriers

The original antidiagonal distribution and total map on the original
coherent-cohomology carriers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

/-- Canonical native distribution, with the original total-degree fibers. -/
def structureTensorTotalSourceEquiv :=
  @DirectSum.totalDegreeSourceEquiv k ‹Field k›
    (structureCohomology k X) (structureCohomology k Y)
    (fun n => (inferInstance : AddCommGroup (structureCohomology k X n)).toAddCommMonoid)
    (structureCohomologyModule X)
    (fun n => (inferInstance : AddCommGroup (structureCohomology k Y n)).toAddCommMonoid)
    (structureCohomologyModule Y)

/-- The direct sum of the original degreewise Kunneth operators. -/
def structureExternalLinearMap :=
  @DirectSum.mapAfterEquivOfCup k ‹Field k›
    (structureCohomology k X) (structureCohomology k Y) (structureCohomology k (X ⊗ Y))
    (fun n => (inferInstance : AddCommGroup (structureCohomology k X n)).toAddCommMonoid)
    (structureCohomologyModule X)
    (fun n => (inferInstance : AddCommGroup (structureCohomology k Y n)).toAddCommMonoid)
    (structureCohomologyModule Y)
    (fun n => (inferInstance :
      AddCommGroup (structureCohomology k (X ⊗ Y) n)).toAddCommMonoid)
    (structureCohomologyModule (X ⊗ Y))
    (structureTensorTotalSourceEquiv X Y) (@structureExternalCup k _ X Y)

end AlgebraicGeometry.Scheme.Cohomology
