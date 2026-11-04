/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Coalgebra.Diagrams
public import Aglib.Algebra.Coalgebra.ComparisonRight

/-! # The coproduct and counit laws on the original maps -/

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

/-- The original multiplication pullbacks and their associativity law. -/
def structureCohomologyMultiplicationDiagram :
    Coalgebra.MultiplicationDiagram k (structureCohomologyAlgebra G)
      (structureCohomologyAlgebra (G ⊗ G)) (structureCohomologyAlgebra ((G ⊗ G) ⊗ G)) where
  mul := structureCohomologyAlgebraPullbackLinear μ[G]
  left := structureCohomologyAlgebraPullbackLinear (μ[G] ⊗ₘ 𝟙 G)
  right := structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ
    structureCohomologyAlgebraPullbackLinear (𝟙 G ⊗ₘ μ[G])
  assoc := group_multiplication_pullback_assoc G

/-- Coassociativity for the original multiplication pullback and Kunneth inverse. -/
abbrev structureCohomologyCoalgebra_coassoc :=
  let h := structureCohomologyCoalgebra_assoc_diagram G
  let hL := structureCohomologyCoalgebra_mul_left_diagram G
  let hR := structureCohomologyCoalgebra_mul_right_diagram G
  let multiplication := structureCohomologyMultiplicationDiagram G
  Coalgebra.coassocFromOriginalDiagrams h multiplication
    (structureCohomologyAlgebraPullbackLinear μ[G])
    (structureCohomologyAlgebraPullbackLinear (μ[G] ⊗ₘ 𝟙 G))
    hL hR rfl rfl rfl rfl

/-- The left counit equation for the original augmentation. -/
abbrev structureCohomologyCoalgebra_leftCounit :=
  let hPoint := structureCohomologyCoalgebra_point_left_diagram G
  let hUnit := group_multiplication_pullback_unit_left G
  LinearEquiv.left_counit_of_product_diagram (structureExternalLinearEquiv G G)
    (structureCohomologyAlgebraPullbackLinear μ[G])
    (structureCohomologyAugmentationLinear G)
    (structureCohomologyAlgebraPullbackLinear (lift (toUnit G ≫ η[G]) (𝟙 G))) hPoint hUnit

/-- The right counit equation for the original augmentation. -/
abbrev structureCohomologyCoalgebra_rightCounit :=
  let hPoint := structureCohomologyCoalgebra_point_right_diagram G
  let hUnit := group_multiplication_pullback_unit_right G
  LinearEquiv.right_counit_of_product_diagram (structureExternalLinearEquiv G G)
    (structureCohomologyAlgebraPullbackLinear μ[G])
    (structureCohomologyAugmentationLinear G)
    (structureCohomologyAlgebraPullbackLinear (lift (𝟙 G) (toUnit G ≫ η[G]))) hPoint hUnit

end AlgebraicGeometry.Scheme.Cohomology
