/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Map

/-!
# Original values of the total Kunneth operator

Evaluate the chosen total-degree source map and the original degreewise
Kunneth operator on a homogeneous tensor.
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

local notation "originalTotalValue(" k ", " X ", " Y ", " p ", " q ", " n ", " h ", " x ", " y
    ")" =>
  @DirectSum.mapAfterEquivOfCup_tmul k ‹Field k›
    (structureCohomology k X) (structureCohomology k Y) (structureCohomology k (X ⊗ Y))
    (fun i => @AddCommGroup.toAddCommMonoid (structureCohomology k X i)
      (inferInstance : AddCommGroup (structureCohomology k X i)))
    (structureCohomologyModule X)
    (fun i => @AddCommGroup.toAddCommMonoid (structureCohomology k Y i)
      (inferInstance : AddCommGroup (structureCohomology k Y i)))
    (structureCohomologyModule Y)
    (fun i => @AddCommGroup.toAddCommMonoid (structureCohomology k (X ⊗ Y) i)
      (inferInstance : AddCommGroup (structureCohomology k (X ⊗ Y) i)))
    (structureCohomologyModule (X ⊗ Y))
    (structureTensorTotalSourceEquiv X Y)
    rfl (@structureExternalCup k _ X Y) (structureExternalLinearMap X Y) rfl p q n h x y

/-- The original total operator has the original homogeneous external-cup value. -/
theorem structureExternalLinearMap_tmul {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    type_of% (originalTotalValue(k, X, Y, p, q, n, h, x, y)) :=
  originalTotalValue(k, X, Y, p, q, n, h, x, y)

end AlgebraicGeometry.Scheme.Cohomology
