/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Coherence
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Point
public import Aglib.AlgebraicGeometry.Cohomology.Group.Multiplication
public import Aglib.AlgebraicGeometry.Group.StructureMaps
public import Aglib.Algebra.Coalgebra.Comparison

/-!
# The original multiplication pullback and point laws

The one original Kunneth inverse and the actual group multiplication define
comultiplication. The complete product diagrams discharge coassociativity.
The existing augmentation is the counit, by evaluation at the actual identity
section. That evaluation remains linear and never requires a flat identity.
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

variable {k : Type u} [Field k]

variable (G : FScheme k) [GrpObj G]

local instance : Flat (μ[G]).left := AlgebraicGeometry.Scheme.Group.flat_mul G

variable [IsProper G.hom] [GeometricallyIntegral G.hom]

local instance : IsProper (G ⊗ G).hom := by
  dsimp
  infer_instance

omit [GrpObj G] [GeometricallyIntegral G.hom] in
/-- The selected total comparison satisfies the original whole associativity diagram. -/
theorem structureCohomologyCoalgebra_assoc_diagram :
    (structureExternalLinearEquiv (G ⊗ G) G).toLinearMap ∘ₗ
        (structureExternalLinearEquiv G G).toLinearMap.rTensor
          (structureCohomologyAlgebra G) =
      (structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ
        (structureExternalLinearEquiv G (G ⊗ G)).toLinearMap) ∘ₗ
        (structureExternalLinearEquiv G G).toLinearMap.lTensor
          (structureCohomologyAlgebra G) ∘ₗ
        (TensorProduct.assoc k (structureCohomologyAlgebra G)
          (structureCohomologyAlgebra G) (structureCohomologyAlgebra G)).toLinearMap := by
  have h := structureExternalLinearMap_assoc G G G
  simpa only [structureExternalLinearEquiv_toLinearMap,
    LinearMap.comp_assoc] using h

omit [GeometricallyIntegral G.hom] in
/-- Multiplication pullback obeys the original left external-product diagram. -/
theorem structureCohomologyCoalgebra_mul_left_diagram :
    structureCohomologyAlgebraPullbackLinear (μ[G] ⊗ₘ 𝟙 G) ∘ₗ
        (structureExternalLinearEquiv G G).toLinearMap =
      (structureExternalLinearEquiv (G ⊗ G) G).toLinearMap ∘ₗ
        (structureCohomologyAlgebraPullbackLinear μ[G]).rTensor
          (structureCohomologyAlgebra G) := by
  have h := structureExternalLinearMap_naturality μ[G] (𝟙 G)
  simpa only [structureExternalLinearEquiv_toLinearMap,
    structureCohomologyAlgebraPullbackLinear_id, LinearMap.rTensor,
    LinearMap.comp_assoc] using h

omit [GeometricallyIntegral G.hom] in
/-- Multiplication pullback obeys the original right external-product diagram. -/
theorem structureCohomologyCoalgebra_mul_right_diagram :
    (structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ
        structureCohomologyAlgebraPullbackLinear (𝟙 G ⊗ₘ μ[G])) ∘ₗ
        (structureExternalLinearEquiv G G).toLinearMap =
      (structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ
        (structureExternalLinearEquiv G (G ⊗ G)).toLinearMap) ∘ₗ
        (structureCohomologyAlgebraPullbackLinear μ[G]).lTensor
          (structureCohomologyAlgebra G) := by
  have h := congrArg
    (fun f => structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ f)
    (structureExternalLinearMap_naturality (𝟙 G) μ[G])
  simpa only [structureExternalLinearEquiv_toLinearMap,
    structureCohomologyAlgebraPullbackLinear_id, LinearMap.lTensor,
    LinearMap.comp_assoc] using h

/-- Evaluation at the actual identity is the original left counit diagram. -/
theorem structureCohomologyCoalgebra_point_left_diagram :
    structureCohomologyAlgebraPullbackLinear (lift (toUnit G ≫ η[G]) (𝟙 G)) ∘ₗ
        (structureExternalLinearEquiv G G).toLinearMap =
      (TensorProduct.lid k (structureCohomologyAlgebra G)).toLinearMap ∘ₗ
        (structureCohomologyAugmentationLinear G).rTensor
          (structureCohomologyAlgebra G) := by
  simpa only [structureExternalLinearEquiv_toLinearMap] using
    structureExternalLinearMap_point_left G G η[G]

/-- Evaluation at the actual identity is the original right counit diagram. -/
theorem structureCohomologyCoalgebra_point_right_diagram :
    structureCohomologyAlgebraPullbackLinear (lift (𝟙 G) (toUnit G ≫ η[G])) ∘ₗ
        (structureExternalLinearEquiv G G).toLinearMap =
      (TensorProduct.rid k (structureCohomologyAlgebra G)).toLinearMap ∘ₗ
        (structureCohomologyAugmentationLinear G).lTensor
          (structureCohomologyAlgebra G) := by
  simpa only [structureExternalLinearEquiv_toLinearMap] using
    structureExternalLinearMap_point_right G G η[G]

/-- The native coalgebra uses ONE original Kunneth inverse and the original augmentation. -/
instance structureCohomologyCoalgebra : Coalgebra k (structureCohomologyAlgebra G) := by
  exact Coalgebra.ofTensorComparison
    (structureExternalLinearEquiv G G) (structureExternalLinearEquiv (G ⊗ G) G)
    (structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ
      (structureExternalLinearEquiv G (G ⊗ G)).toLinearMap)
    (structureCohomologyAlgebraPullbackLinear μ[G])
    (structureCohomologyAlgebraPullbackLinear (μ[G] ⊗ₘ 𝟙 G))
    (structureCohomologyAlgebraPullbackLinear (α_ G G G).hom ∘ₗ
      structureCohomologyAlgebraPullbackLinear (𝟙 G ⊗ₘ μ[G]))
    (structureCohomologyAugmentationLinear G)
    (structureCohomologyAlgebraPullbackLinear (lift (toUnit G ≫ η[G]) (𝟙 G)))
    (structureCohomologyAlgebraPullbackLinear (lift (𝟙 G) (toUnit G ≫ η[G])))
    (structureCohomologyCoalgebra_assoc_diagram G)
    (structureCohomologyCoalgebra_mul_left_diagram G)
    (structureCohomologyCoalgebra_mul_right_diagram G)
    (group_multiplication_pullback_assoc G)
    (structureCohomologyCoalgebra_point_left_diagram G)
    (structureCohomologyCoalgebra_point_right_diagram G)
    (group_multiplication_pullback_unit_left G)
    (group_multiplication_pullback_unit_right G)

/-- The actual comultiplication is the original multiplication pullback followed by κ inverse. -/
theorem structureCohomologyCoalgebra_comul :
    Coalgebra.comul (R := k) = (structureExternalLinearEquiv G G).symm.toLinearMap ∘ₗ
      structureCohomologyAlgebraPullbackLinear μ[G] := rfl

/-- The actual counit is exactly the existing augmentation with its existing field action. -/
theorem structureCohomologyCoalgebra_counit :
    Coalgebra.counit (R := k) = structureCohomologyAugmentationLinear G := rfl

end AlgebraicGeometry.Scheme.Cohomology
