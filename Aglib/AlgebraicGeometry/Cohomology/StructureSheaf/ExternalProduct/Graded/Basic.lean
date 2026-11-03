/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Ext
public import Aglib.Algebra.Graded.ExternalProduct

/-!
# The signed algebra map of the original external product

The complete native graded-family constructor is specialized to the original
cup and projection pullbacks. All its inputs are the already proved original
multiplication, inclusion and signed crossing equations. No extra geometric
compatibility datum or Künneth hypothesis enters this construction.
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

local instance : Flat (fst X Y).left := structureProduct_fst_flat X Y
local instance : Flat (snd X Y).left := structureProduct_snd_flat X Y

/-- The original external product as a homomorphism from the native
Koszul-signed tensor algebra, using the complete generic construction. -/
def structureExternalAlgebraMap :=
  DirectSum.externalProductAlgHom (R := k)
    (M := structureCohomology k X) (N := structureCohomology k Y)
    (P := structureCohomology k (X ⊗ Y))
    (gradeM := structureCohomologyGradedAlgebra X)
    (gradeN := structureCohomologyGradedAlgebra Y)
    (@structureCup k _ (X ⊗ Y))
    (@structureCohomologyInclusion_mul k _ (X ⊗ Y))
    (structureCohomologyAlgebraPullback (fst X Y))
    (structureCohomologyAlgebraPullback (snd X Y))
    (structureCohomologyPullbackLinear (fst X Y))
    (structureCohomologyPullbackLinear (snd X Y))
    (structureCohomologyAlgebraPullback_inclusion (fst X Y))
    (structureCohomologyAlgebraPullback_inclusion (snd X Y))
    (@structureCup_fst_snd_comm k _ X Y)

/-- Mathlib's original source identification uses exactly the constructor-selected grading. -/
def structureExternalTensorSourceEquiv :=
  DirectSum.externalProductSourceEquiv (R := k)
    (M := structureCohomology k X) (N := structureCohomology k Y)
    (gradeM := structureCohomologyGradedAlgebra X)
    (gradeN := structureCohomologyGradedAlgebra Y)

private theorem structureExternalAlgebraMap_pure :
    DirectSum.ExternalProductPureEq (structureExternalAlgebraMap X Y)
      (structureCohomologyAlgebraPullback (fst X Y))
      (structureCohomologyAlgebraPullback (snd X Y)) := by
  exact DirectSum.externalProductAlgHom_pureEq
    (gradeM := structureCohomologyGradedAlgebra X)
    (gradeN := structureCohomologyGradedAlgebra Y)
    (@structureCup k _ (X ⊗ Y))
    (@structureCohomologyInclusion_mul k _ (X ⊗ Y))
    (structureCohomologyAlgebraPullback (fst X Y))
    (structureCohomologyAlgebraPullback (snd X Y))
    (structureCohomologyPullbackLinear (fst X Y))
    (structureCohomologyPullbackLinear (snd X Y))
    (structureCohomologyAlgebraPullback_inclusion (fst X Y))
    (structureCohomologyAlgebraPullback_inclusion (snd X Y))
    (@structureCup_fst_snd_comm k _ X Y)

private theorem structureExternalAlgebraMap_homogeneous :
    DirectSum.ExternalProductHomogeneousEq (structureExternalAlgebraMap X Y)
      (@structureExternalCup k _ X Y) := by
  exact DirectSum.ExternalProductPureEq.toHomogeneousEq
    (structureExternalAlgebraMap_pure X Y)
    (@structureCup k _ (X ⊗ Y))
    (@structureCohomologyInclusion_mul k _ (X ⊗ Y))
    (structureCohomologyPullbackLinear (fst X Y))
    (structureCohomologyPullbackLinear (snd X Y))
    (structureCohomologyAlgebraPullback_inclusion (fst X Y))
    (structureCohomologyAlgebraPullback_inclusion (snd X Y))
    (@structureExternalCup k _ X Y) (@structureExternalCup_apply k _ X Y)

/-- The selected source map retains its literal pure signed tensor. -/
theorem structureExternalTensorSourceEquiv_tmul
    (a : structureCohomologyAlgebra X) (b : structureCohomologyAlgebra Y) :
    structureExternalTensorSourceEquiv X Y (a ⊗ₜ[k] b) = a ᵍ⊗ₜ[k] b := by
  exact DirectSum.externalProductSourceEquiv_tmul
    (R := k) (M := structureCohomology k X) (N := structureCohomology k Y)
    (gradeM := structureCohomologyGradedAlgebra X)
    (gradeN := structureCohomologyGradedAlgebra Y) a b

/-- Every pure homogeneous tensor has the original external-cup value. -/
@[simp]
theorem structureExternalAlgebraMap_tmul {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureExternalAlgebraMap X Y
        (structureCohomologyInclusion X p x ᵍ⊗ₜ[k] structureCohomologyInclusion Y q y) =
      structureCohomologyInclusion (X ⊗ Y) n (structureExternalCup X Y h x y) := by
  exact DirectSum.ExternalProductHomogeneousEq.apply
    (R := k) (M := structureCohomology k X) (N := structureCohomology k Y)
    (P := structureCohomology k (X ⊗ Y))
    (structureExternalAlgebraMap_homogeneous X Y) h x y

/-- The original selected signed-tensor identification preserves its actual unit. -/
theorem structureExternalTensorSourceEquiv_one :
    structureExternalTensorSourceEquiv X Y
      ((1 : structureCohomologyAlgebra X) ⊗ₜ[k] (1 : structureCohomologyAlgebra Y)) = 1 := by
  exact DirectSum.externalProductSourceEquiv_one
    (R := k) (M := structureCohomology k X) (N := structureCohomology k Y)
    (gradeM := structureCohomologyGradedAlgebra X)
    (gradeN := structureCohomologyGradedAlgebra Y)

end AlgebraicGeometry.Scheme.Cohomology
