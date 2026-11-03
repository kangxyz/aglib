/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Values
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup.PullbackLinear
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Coherence
public import Aglib.Algebra.Graded.TensorProduct.Coherence

/-!
# Whole coherence of the one original total Kunneth operator

The chosen native operator has the original homogeneous values, product
naturality and associativity. Original unrestricted pullback laws are imported
from their lower owner before group coalgebra assembly.
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

variable {k : Type u} [Field k] (X Y Z : FScheme k)

set_option maxHeartbeats 1000000 in
-- Native whole flat-pullback specialization exceeds the standard budget.
/-- The entire original total operator has flat geometric naturality. -/
theorem structureExternalLinearMap_naturality
    {X₀ X₁ Y₀ Y₁ : FScheme k} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    [Flat f.left] [Flat g.left] :
    structureCohomologyAlgebraPullbackLinear (f ⊗ₘ g) ∘ₗ
        structureExternalLinearMap X₁ Y₁ =
      structureExternalLinearMap X₀ Y₀ ∘ₗ TensorProduct.map
        (structureCohomologyAlgebraPullbackLinear f)
        (structureCohomologyAlgebraPullbackLinear g) := by
  apply DirectSum.tensorDirectSum_ext (R := k) (structureCohomology k X₁) (structureCohomology k Y₁)
  intro p q x y
  change structureCohomologyAlgebraPullbackLinear (f ⊗ₘ g)
      (structureExternalLinearMap X₁ Y₁
        (structureCohomologyInclusion X₁ p x ⊗ₜ[k] structureCohomologyInclusion Y₁ q y)) =
    structureExternalLinearMap X₀ Y₀
      (structureCohomologyAlgebraPullbackLinear f (structureCohomologyInclusion X₁ p x) ⊗ₜ[k]
        structureCohomologyAlgebraPullbackLinear g (structureCohomologyInclusion Y₁ q y))
  rw [structureExternalLinearMap_tmul X₁ Y₁ rfl,
    structureCohomologyAlgebraPullbackLinear_inclusion,
    structureCohomologyAlgebraPullbackLinear_inclusion,
    structureCohomologyAlgebraPullbackLinear_inclusion,
    structureExternalLinearMap_tmul X₀ Y₀ rfl]
  exact congrArg (structureCohomologyInclusion (X₀ ⊗ Y₀) (p + q))
    (structureExternalCup_naturality f g rfl x y)

/-- The whole tensor associativity diagram is the original external-cup associativity. -/
theorem structureExternalLinearMap_assoc :
    structureExternalLinearMap (X ⊗ Y) Z ∘ₗ (structureExternalLinearMap X Y).rTensor
        (structureCohomologyAlgebra Z) =
      structureCohomologyAlgebraPullbackLinear (α_ X Y Z).hom ∘ₗ
        structureExternalLinearMap X (Y ⊗ Z) ∘ₗ
        (structureExternalLinearMap Y Z).lTensor (structureCohomologyAlgebra X) ∘ₗ
        (TensorProduct.assoc k (structureCohomologyAlgebra X)
          (structureCohomologyAlgebra Y) (structureCohomologyAlgebra Z)).toLinearMap := by
  exact DirectSum.tensorTotalMap_assoc_of_values
    (R := k)
    (structureCohomology k X) (structureCohomology k Y) (structureCohomology k Z)
    (structureCohomology k (X ⊗ Y)) (structureCohomology k (Y ⊗ Z))
    (structureCohomology k (X ⊗ (Y ⊗ Z)))
    (structureCohomology k ((X ⊗ Y) ⊗ Z))
    (structureExternalLinearMap X Y) (structureExternalLinearMap (X ⊗ Y) Z)
    (structureExternalLinearMap Y Z) (structureExternalLinearMap X (Y ⊗ Z))
    (structureCohomologyAlgebraPullbackLinear (α_ X Y Z).hom)
    (fun i j d h x y => structureExternalCup X Y h x y)
    (fun d r n h x z => structureExternalCup (X ⊗ Y) Z h x z)
    (fun j r d h y z => structureExternalCup Y Z h y z)
    (fun i d n h x y => structureExternalCup X (Y ⊗ Z) h x y)
    (fun n => structureCohomologyPullbackLinear (α_ X Y Z).hom n)
    (fun i j d h x y => structureExternalLinearMap_tmul X Y h x y)
    (fun d r n h x z => structureExternalLinearMap_tmul (X ⊗ Y) Z h x z)
    (fun j r d h y z => structureExternalLinearMap_tmul Y Z h y z)
    (fun i d n h x y => structureExternalLinearMap_tmul X (Y ⊗ Z) h x y)
    (fun n x => structureCohomologyAlgebraPullbackLinear_inclusion (α_ X Y Z).hom n x)
    (fun i j r x y z => (structureExternalCup_assoc X Y Z rfl rfl rfl x y z).symm)

end AlgebraicGeometry.Scheme.Cohomology
