/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup.PullbackLinear
public import Aglib.AlgebraicGeometry.Group.StructureMaps

/-!
# Original multiplication pullback diagrams on a group scheme

The unrestricted whole cohomology pullback sends the actual group
associativity and unit laws to three linear-map equations. The identity
section is never assumed flat.
-/

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

variable {k : Type u} [Field k] (G : FScheme k) [GrpObj G]

theorem group_multiplication_pullback_assoc :
    structureCohomologyAlgebraPullbackLinear (μ[G] ⊗ₘ 𝟙 G) ∘ₗ
        structureCohomologyAlgebraPullbackLinear μ[G] =
      (structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ
        structureCohomologyAlgebraPullbackLinear (𝟙 G ⊗ₘ μ[G])) ∘ₗ
        structureCohomologyAlgebraPullbackLinear μ[G] := by
  have hGroup := MonObj.mul_assoc G
  have hNative := congrArg (fun f => structureCohomologyAlgebraPullbackLinear f) hGroup
  simp only [structureCohomologyAlgebraPullbackLinear_comp, LinearMap.comp_assoc,
    tensorHom_id, id_tensorHom] at hNative ⊢
  exact hNative

theorem group_multiplication_pullback_unit_left :
    structureCohomologyAlgebraPullbackLinear (lift (toUnit G ≫ η[G]) (𝟙 G)) ∘ₗ
      structureCohomologyAlgebraPullbackLinear μ[G] = LinearMap.id := by
  rw [← structureCohomologyAlgebraPullbackLinear_comp,
    MonObj.lift_comp_one_left, structureCohomologyAlgebraPullbackLinear_id]

theorem group_multiplication_pullback_unit_right :
    structureCohomologyAlgebraPullbackLinear (lift (𝟙 G) (toUnit G ≫ η[G])) ∘ₗ
      structureCohomologyAlgebraPullbackLinear μ[G] = LinearMap.id := by
  rw [← structureCohomologyAlgebraPullbackLinear_comp,
    MonObj.lift_comp_one_right, structureCohomologyAlgebraPullbackLinear_id]

end AlgebraicGeometry.Scheme.Cohomology
