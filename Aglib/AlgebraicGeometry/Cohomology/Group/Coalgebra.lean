/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Coalgebra.Basic
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Support

/-!
# Product and degree laws of the original coherent-cohomology coalgebra

The one native comultiplication retains the original signed tensor product,
unit, and total-degree-one antidiagonal.
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
  [IsProper G.hom] [GeometricallyIntegral G.hom]

local instance : Flat (μ[G]).left := AlgebraicGeometry.Scheme.Group.flat_mul G

/-- The original coproduct sends the original unit to its original pure tensor. -/
theorem structureCohomologyComul_one :
    Coalgebra.comul (R := k) (1 : structureCohomologyAlgebra G) =
      (1 : structureCohomologyAlgebra G) ⊗ₜ[k] (1 : structureCohomologyAlgebra G) := by
  have ht : structureExternalTensorSourceEquiv G G
      ((1 : structureCohomologyAlgebra G) ⊗ₜ[k] (1 : structureCohomologyAlgebra G)) = 1 := by
    exact structureExternalTensorSourceEquiv_one G G
  have hNative := LinearEquiv.inverse_one_of_algebra_comparison
    (structureExternalLinearEquiv G G) (structureExternalTensorSourceEquiv G G)
    (structureExternalAlgebraMap G G) (structureExternalAlgebraMap_linear G G)
    (structureCohomologyAlgebraPullback μ[G]) ht
  have hLinear := LinearMap.congr_fun
    (structureCohomologyAlgebraPullback_toLinearMap μ[G]) 1
  simp only [AlgHom.toLinearMap_apply] at hLinear
  have hValue := congrArg (structureExternalLinearEquiv G G).symm hLinear
  have hFinal := hValue.symm.trans hNative
  simp only [structureCohomologyCoalgebra_comul, LinearMap.comp_apply]
  exact hFinal

/-- Multiplication of the actual coproduct uses the original Koszul-signed tensor. -/
theorem structureCohomologyComul_mul (a b : structureCohomologyAlgebra G) :
    structureExternalTensorSourceEquiv G G (Coalgebra.comul (R := k) (a * b)) =
      structureExternalTensorSourceEquiv G G (Coalgebra.comul (R := k) a) *
        structureExternalTensorSourceEquiv G G (Coalgebra.comul (R := k) b) := by
  have hNative := LinearEquiv.inverse_mul_of_algebra_comparison
    (structureExternalLinearEquiv G G) (structureExternalTensorSourceEquiv G G)
    (structureExternalAlgebraMap G G) (structureExternalAlgebraMap_linear G G)
    (structureCohomologyAlgebraPullback μ[G]) a b
  have hLinear := structureCohomologyAlgebraPullback_toLinearMap μ[G]
  have hA := LinearMap.congr_fun hLinear a
  have hB := LinearMap.congr_fun hLinear b
  have hAB := LinearMap.congr_fun hLinear (a * b)
  simp only [AlgHom.toLinearMap_apply] at hA hB hAB
  have hValueA := congrArg
    (fun z => structureExternalTensorSourceEquiv G G
      ((structureExternalLinearEquiv G G).symm z)) hA
  have hValueB := congrArg
    (fun z => structureExternalTensorSourceEquiv G G
      ((structureExternalLinearEquiv G G).symm z)) hB
  have hValueAB := congrArg
    (fun z => structureExternalTensorSourceEquiv G G
      ((structureExternalLinearEquiv G G).symm z)) hAB
  have hFinal := hValueAB.symm.trans
    (hNative.trans (congrArg₂ (· * ·) hValueA hValueB))
  simp only [structureCohomologyCoalgebra_comul, LinearMap.comp_apply]
  exact hFinal

set_option maxHeartbeats 1000000 in
-- The final comparison of the original inverse-support law with the native
-- degree-one projections exceeds the standard budget; keep this finite
-- allowance local to the law.
/-- Degree one has exactly its two original possible tensor bidegrees. -/
theorem structureCohomologyComul_degreeOne (x : structureCohomologyGrade G 1) :
    TensorProduct.map (GradedAlgebra.proj (structureCohomologyGrade G) 0)
        (GradedAlgebra.proj (structureCohomologyGrade G) 1) (Coalgebra.comul (x : _)) +
      TensorProduct.map (GradedAlgebra.proj (structureCohomologyGrade G) 1)
        (GradedAlgebra.proj (structureCohomologyGrade G) 0) (Coalgebra.comul (x : _)) =
      Coalgebra.comul (x : structureCohomologyAlgebra G) := by
  let z := (structureCohomologyGradeEquiv G 1).symm x
  have hz : structureCohomologyInclusion G 1 z = (x : structureCohomologyAlgebra G) := by
    have hNative := congrArg (fun a : structureCohomologyGrade G 1 =>
      (a : structureCohomologyAlgebra G)) ((structureCohomologyGradeEquiv G 1).apply_symm_apply x)
    simp only [structureCohomologyGradeEquiv_apply] at hNative
    exact hNative
  let w := structureCohomologyPullbackLinear μ[G] 1 z
  have hProjection := DirectSum.equivAfterEquiv_symm_degreeOne_apply_of_source
    (R := k) (structureTensorTotalSourceEquiv G G) rfl
    (structureKunnethDegreeEquiv G G)
    (structureExternalLinearEquiv G G) rfl w
  have hPr (i : ℕ) : GradedAlgebra.proj (structureCohomologyGrade G) i =
      structureCohomologyInclusion G i ∘ₗ structureCohomologyComponent G i := by
    apply LinearMap.ext
    intro a
    exact structureCohomology_proj G i a
  rw [← hz]
  simp only [hPr, structureCohomologyCoalgebra_comul,
    LinearMap.comp_apply,
    structureCohomologyAlgebraPullbackLinear_inclusion] at hProjection ⊢
  exact hProjection

end AlgebraicGeometry.Scheme.Cohomology
