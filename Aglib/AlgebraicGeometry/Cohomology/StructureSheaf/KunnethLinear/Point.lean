/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Values
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Point
public import Aglib.AlgebraicGeometry.Cohomology.Group.Augmentation

/-!
# Whole point laws for the original total Kunneth operator

The original augmentation and unrestricted pullback along a point give both
whole tensor-unit diagrams. The point section is not required to be flat.
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

private theorem augmentationLinear_inclusion_zero (X : FScheme k)
    [IsProper X.hom] [GeometricallyIntegral X.hom] (x : structureCohomology k X 0) :
    structureCohomologyAugmentationLinear X (structureCohomologyInclusion X 0 x) =
      (structureH0ScalarEquiv X).symm x := by
  change (structureH0ScalarEquiv X).symm
    (structureCohomologyComponent X 0 (structureCohomologyInclusion X 0 x)) = _
  rw [structureCohomologyComponent_inclusion]

private theorem augmentationLinear_inclusion_succ (X : FScheme k)
    [IsProper X.hom] [GeometricallyIntegral X.hom] (p : ℕ)
    (x : structureCohomology k X (p + 1)) :
    structureCohomologyAugmentationLinear X (structureCohomologyInclusion X (p + 1) x) = 0 := by
  change (structureH0ScalarEquiv X).symm
    ((DirectSum.of (structureCohomology k X) (p + 1) x) 0) = 0
  rw [DirectSum.of_eq_of_ne (p + 1) 0 x (by omega), map_zero]

set_option maxHeartbeats 1000000 in
-- The original whole point diagram requires a finite local allowance when
-- comparing its tensor and pullback values; the point is never made flat.
/-- The complete left point diagram uses the original augmentation and no flat point. -/
theorem structureExternalLinearMap_point_left (X Y : FScheme k)
    [IsProper X.hom] [GeometricallyIntegral X.hom] (e : 𝟙_ (FScheme k) ⟶ X) :
    structureCohomologyAlgebraPullbackLinear (lift (toUnit Y ≫ e) (𝟙 Y)) ∘ₗ
        structureExternalLinearMap X Y =
      (TensorProduct.lid k (structureCohomologyAlgebra Y)).toLinearMap ∘ₗ
        (structureCohomologyAugmentationLinear X).rTensor (structureCohomologyAlgebra Y) := by
  apply DirectSum.tensorDirectSum_ext (structureCohomology k X) (structureCohomology k Y)
  intro p q x y
  simp only [LinearMap.comp_apply, LinearMap.rTensor, TensorProduct.map_tmul,
    LinearMap.id_apply]
  cases p with
  | zero =>
    rw [structureExternalLinearMap_tmul X Y (Nat.zero_add q),
      structureCohomologyAlgebraPullbackLinear_inclusion,
      structureExternalCup_point_left_zero X Y e, augmentationLinear_inclusion_zero,
      LinearMap.map_smul]
    exact (TensorProduct.lid_tmul
      (structureCohomologyInclusion Y q y) ((structureH0ScalarEquiv X).symm x)).symm
  | succ p =>
    rw [structureExternalLinearMap_tmul X Y rfl,
      structureCohomologyAlgebraPullbackLinear_inclusion,
      structureExternalCup_point_left_succ X Y e rfl,
      map_zero, augmentationLinear_inclusion_succ]
    rw [TensorProduct.zero_tmul]
    exact ((TensorProduct.lid k (structureCohomologyAlgebra Y)).toLinearMap.map_zero).symm

set_option maxHeartbeats 1000000 in
-- The symmetric whole point diagram has the same measured native conversion cost.
/-- The complete right point diagram is the original other counit diagram. -/
theorem structureExternalLinearMap_point_right (X Y : FScheme k)
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (e : 𝟙_ (FScheme k) ⟶ Y) :
    structureCohomologyAlgebraPullbackLinear (lift (𝟙 X) (toUnit X ≫ e)) ∘ₗ
        structureExternalLinearMap X Y =
      (TensorProduct.rid k (structureCohomologyAlgebra X)).toLinearMap ∘ₗ
        (structureCohomologyAugmentationLinear Y).lTensor (structureCohomologyAlgebra X) := by
  apply DirectSum.tensorDirectSum_ext (structureCohomology k X) (structureCohomology k Y)
  intro p q x y
  simp only [LinearMap.comp_apply, LinearMap.lTensor, TensorProduct.map_tmul,
    LinearMap.id_apply]
  cases q with
  | zero =>
    rw [structureExternalLinearMap_tmul X Y (Nat.add_zero p),
      structureCohomologyAlgebraPullbackLinear_inclusion,
      structureExternalCup_point_right_zero X Y e, augmentationLinear_inclusion_zero,
      LinearMap.map_smul]
    exact (TensorProduct.rid_tmul
      (structureCohomologyInclusion X p x) ((structureH0ScalarEquiv Y).symm y)).symm
  | succ q =>
    rw [structureExternalLinearMap_tmul X Y rfl,
      structureCohomologyAlgebraPullbackLinear_inclusion,
      structureExternalCup_point_right_succ X Y e rfl,
      map_zero, augmentationLinear_inclusion_succ]
    rw [TensorProduct.tmul_zero]
    exact ((TensorProduct.rid k (structureCohomologyAlgebra X)).toLinearMap.map_zero).symm

end AlgebraicGeometry.Scheme.Cohomology
