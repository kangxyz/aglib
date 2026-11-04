/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Factorization
public import Aglib.Algebra.Graded.TensorProduct.DegreeEquiv

/-! # The original total Kunneth inverse -/

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
local notation "withKunnethDictionaries(" f ", " k ", " X ", " Y ")" =>
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

/-- Compose the original source distribution with the original degreewise inverses. -/
def structureExternalLinearEquiv :=
  withKunnethDictionaries(DirectSum.totalEquivWithGivenForward, k, X, Y)
    (structureKunnethMap X Y) (structureKunnethMap_bijective X Y)
    (structureTensorTotalSourceEquiv X Y) (structureExternalLinearMap X Y)
    (structureExternalLinearMap_factorization X Y)

end AlgebraicGeometry.Scheme.Cohomology
