/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Coalgebra.Basic
public import Aglib.Algebra.Coalgebra.Multiplicativity
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethComparison
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Support

/-!
# Product and degree laws of the original coherent-cohomology coalgebra

The one native comultiplication retains the original signed tensor product,
unit, and total-degree-one antidiagonal.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : FScheme k) [GrpObj G]
  [IsProper G.hom] [GeometricallyIntegral G.hom]

local instance : Flat (μ[G]).left := AlgebraicGeometry.Scheme.Group.flat_mul G

private theorem structureCohomologyComul_comparison :
    Function.Injective (structureExternalAlgebraMap G G) ∧
      ∀ a : structureCohomologyAlgebra G,
        structureExternalAlgebraMap G G
            (structureExternalTensorSourceEquiv G G (Coalgebra.comul (R := k) a)) =
          structureCohomologyAlgebraPullback μ[G] a := by
  let h := structureExternalAlgebraMap_linear G G
  exact DirectSum.inverse_comparison_properties_of_signed h
    (structureCohomologyAlgebraPullback μ[G]) (structureCohomologyAlgebraPullbackLinear μ[G])
    (structureCohomologyAlgebraPullback_toLinearMap μ[G])
    (Coalgebra.comul (R := k)) (structureCohomologyCoalgebra_comul G)

/-- The original coproduct sends the original unit to its original pure tensor. -/
theorem structureCohomologyComul_one :
    Coalgebra.comul (R := k) (1 : structureCohomologyAlgebra G) =
      (1 : structureCohomologyAlgebra G) ⊗ₜ[k] (1 : structureCohomologyAlgebra G) := by
  exact LinearEquiv.comul_one_of_comparison_properties
    (structureExternalTensorSourceEquiv G G) (structureExternalAlgebraMap G G)
    (structureCohomologyAlgebraPullback μ[G]) (Coalgebra.comul (R := k))
    (structureCohomologyComul_comparison G) (structureExternalTensorSourceEquiv_one G G)

/-- The whole multiplicativity property uses the original coproduct and signed source. -/
theorem structureCohomologyComul_multiplicative :
    LinearMap.IsMultiplicativeAfter (Coalgebra.comul (R := k))
      (structureExternalTensorSourceEquiv G G) := by
  exact LinearMap.isMultiplicativeAfter_of_comparison_properties
    (structureExternalAlgebraMap G G) (structureCohomologyAlgebraPullback μ[G])
    (Coalgebra.comul (R := k)) (structureExternalTensorSourceEquiv G G)
    (structureCohomologyComul_comparison G)

/-- Multiplication of the actual coproduct uses the original Koszul-signed tensor. -/
theorem structureCohomologyComul_mul (a b : structureCohomologyAlgebra G) :
    structureExternalTensorSourceEquiv G G (Coalgebra.comul (R := k) (a * b)) =
      structureExternalTensorSourceEquiv G G (Coalgebra.comul (R := k) a) *
        structureExternalTensorSourceEquiv G G (Coalgebra.comul (R := k) b) := by
  exact (structureCohomologyComul_multiplicative G).apply a b

omit [GeometricallyIntegral G.hom] in
/-- Degree one has exactly its two original possible tensor bidegrees. -/
theorem structureCohomologyComul_degreeOne [GeometricallyIntegral G.hom]
    (x : structureCohomologyGrade G 1) :
    DirectSum.InversePullbackDegreeOneSupport
      (M := structureCohomology k G) (P := structureCohomology k (G ⊗ G))
      (structureExternalLinearEquiv G G) (structureCohomologyAlgebraPullbackLinear μ[G]) x := by
  exact DirectSum.inverse_pullback_degreeOne_of_inverse_inclusion
    (fieldR := (inferInstance : Field k)) (M := structureCohomology k G)
    (groupM := fun n => (inferInstance : AddCommGroup (structureCohomology k G n)))
    (moduleM := structureCohomologyModule G)
    (ringM := structureCohomologyGRing G) (algebraM := structureCohomologyGAlgebra G)
    (P := structureCohomology k (G ⊗ G))
    (groupP := fun n => (inferInstance : AddCommGroup (structureCohomology k (G ⊗ G) n)))
    (moduleP := structureCohomologyModule (G ⊗ G))
    (E := structureTensorTotalSourceEquiv G G)
    (C := structureExternalLinearEquiv G G)
    (v := fun z => LinearEquiv.symm (structureKunnethDegreeEquiv G G 1) z)
    (structureExternalLinearEquiv_symm_inclusion G G 1) rfl
    (structureCohomologyAlgebraPullbackLinear μ[G]) (structureCohomologyPullbackLinear μ[G] 1)
    (structureCohomologyAlgebraPullbackLinear_inclusion μ[G] 1) x

end AlgebraicGeometry.Scheme.Cohomology
