/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Basic

/-!
# Original inverse on homogeneous Kunneth classes

The one selected degreewise inverse and total-source inverse retain the
original homogeneous inclusions. Degree-one support is proved at its consumer.
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

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- On every homogeneous class, the inverse is the original antidiagonal inverse. -/
theorem structureExternalLinearEquiv_symm_inclusion (n : ℕ)
    (z : structureCohomology k (X ⊗ Y) n) :
    (structureExternalLinearEquiv X Y).symm (structureCohomologyInclusion (X ⊗ Y) n z) =
      (structureTensorTotalSourceEquiv X Y).symm
        (DirectSum.lof k ℕ _ n ((structureKunnethDegreeEquiv X Y n).symm z)) := by
  exact DirectSum.equivAfterEquiv_symm_lof
    (structureTensorTotalSourceEquiv X Y) (structureKunnethDegreeEquiv X Y) n z

end AlgebraicGeometry.Scheme.Cohomology
