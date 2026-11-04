/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Inverse

/-! # The original degreewise forward map -/

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

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

-- Specialize each operation at the same original cohomology dictionaries.
local notation "withKunnethDegreeData(" f ", " k ", " X ", " Y ")" =>
  @f k ‹Field k›
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
    (structureKunnethMap X Y) (structureKunnethMap_bijective X Y)

local notation "originalDegreeForward(" k ", " X ", " Y ", " n ")" =>
  withKunnethDegreeData(DirectSum.degreeEquivOfBijective_toLinearMap, k, X, Y) (n := n)
    (structureKunnethDegreeEquiv X Y n) rfl

/-- The original degreewise Kunneth map is the forward map. -/
theorem structureKunnethDegreeEquiv_toLinearMap (n : ℕ) :
    type_of% (originalDegreeForward(k, X, Y, n)) :=
  originalDegreeForward(k, X, Y, n)

end AlgebraicGeometry.Scheme.Cohomology
