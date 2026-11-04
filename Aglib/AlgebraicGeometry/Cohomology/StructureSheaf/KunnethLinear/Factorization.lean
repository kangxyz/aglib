/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Map

/-! # Factorization by the original degree maps -/

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

theorem structureExternalLinearMap_factorization :
    DirectSum.MapFactorization (structureExternalLinearMap X Y)
      (structureTensorTotalSourceEquiv X Y) (structureKunnethMap X Y) :=
  @DirectSum.mapAfterEquivOfCup_factorization k ‹Field k›
    (structureCohomology k X) (structureCohomology k Y) (structureCohomology k (X ⊗ Y))
    (fun i => (inferInstance : AddCommGroup (structureCohomology k X i)).toAddCommMonoid)
    (structureCohomologyModule X)
    (fun i => (inferInstance : AddCommGroup (structureCohomology k Y i)).toAddCommMonoid)
    (structureCohomologyModule Y)
    (fun i => (inferInstance : AddCommGroup
      (structureCohomology k (X ⊗ Y) i)).toAddCommMonoid)
    (structureCohomologyModule (X ⊗ Y))
    (structureTensorTotalSourceEquiv X Y) (@structureExternalCup k _ X Y)
    (structureKunnethMap X Y) (fun _ => rfl) (structureExternalLinearMap X Y) rfl

end AlgebraicGeometry.Scheme.Cohomology
