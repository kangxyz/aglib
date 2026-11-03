/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Graded.Basic

/-!
# Whole native signed tensor correspondence

The original homogeneous, source and external tensor value laws imply the
whole tensor equality on the same algebra map and original inclusions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

/-- Whole homogeneous tensor correspondence with the original linear map.
The generic law keeps the inferred parent structures of the selected maps. -/
abbrev structureExternalAlgebraMap_tensor {p q n : ℕ} (h : p + q = n) :=
  AlgHom.comp_linearEquiv_map_eq_of_values
    (structureExternalAlgebraMap X Y) (structureExternalTensorSourceEquiv X Y)
    (structureCohomologyInclusion X p) (structureCohomologyInclusion Y q)
    (structureCohomologyInclusion (X ⊗ Y) n) (structureExternalTensor X Y h)
    (fun a b => a ᵍ⊗ₜ[k] b) (fun x y => structureExternalCup X Y h x y)
    (structureExternalTensorSourceEquiv_tmul X Y)
    (structureExternalAlgebraMap_tmul X Y h)
    (structureExternalTensor_tmul X Y h)

end AlgebraicGeometry.Scheme.Cohomology
