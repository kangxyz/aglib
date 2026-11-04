/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Coalgebra.Laws

/-! # The group coalgebra on the original maps -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

variable (G : FScheme k) [GrpObj G]

local instance : Flat (μ[G]).left := AlgebraicGeometry.Scheme.Group.flat_mul G

variable [IsProper G.hom] [GeometricallyIntegral G.hom]

/-- The native coalgebra uses the original Kunneth inverse and augmentation. -/
@[instance_reducible, instance]
def structureCohomologyCoalgebra :=
  let h := structureCohomologyCoalgebraCoassoc G
  let hL := structureCohomologyCoalgebraLeftCounit G
  let hR := structureCohomologyCoalgebraRightCounit G
  Coalgebra.ofCoassocAndCounit h (structureCohomologyAugmentationLinear G) hL hR

/-- The actual comultiplication is the original multiplication pullback followed by κ inverse. -/
theorem structureCohomologyCoalgebra_comul :
    Coalgebra.comul (R := k) = (structureExternalLinearEquiv G G).symm.toLinearMap ∘ₗ
      structureCohomologyAlgebraPullbackLinear μ[G] := rfl

/-- The actual counit is exactly the existing augmentation with its existing field action. -/
theorem structureCohomologyCoalgebra_counit :
    Coalgebra.counit (R := k) = structureCohomologyAugmentationLinear G := rfl

end AlgebraicGeometry.Scheme.Cohomology
