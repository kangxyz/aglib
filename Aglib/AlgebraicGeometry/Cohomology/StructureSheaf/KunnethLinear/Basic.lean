/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Kunneth
public import Aglib.Algebra.Graded.TensorProduct

/-!
# The one total comparison on the original Kunneth carriers

The native source, total operator and degreewise inverse are typed at the
original cohomology algebra and original finite antidiagonal sums. Their
complete composition reuses the chosen source and original degree maps.
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

variable {k : Type u} [Field k] (X Y : FScheme k)

/-- Canonical native distribution, with the original total-degree fibers. -/
def structureTensorTotalSourceEquiv :
    (structureCohomologyAlgebra X ⊗[k] structureCohomologyAlgebra Y) ≃ₗ[k]
      ⨁ n, structureKunnethSum X Y n :=
  DirectSum.tensorFiberEquiv (R := k) (structureCohomology k X) (structureCohomology k Y)
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The direct sum of the original degreewise Kunneth operators. -/
def structureExternalLinearMap :
    (structureCohomologyAlgebra X ⊗[k] structureCohomologyAlgebra Y) →ₗ[k]
      structureCohomologyAlgebra (X ⊗ Y) :=
  DirectSum.mapAfterEquiv (F := structureKunnethSum X Y)
    (structureTensorTotalSourceEquiv X Y) (structureKunnethMap X Y)

theorem structureExternalLinearMap_factorization :
    DirectSum.MapFactorization (structureExternalLinearMap X Y)
      (structureTensorTotalSourceEquiv X Y) (structureKunnethMap X Y) := by
  exact DirectSum.mapAfterEquiv_factorization
    (structureTensorTotalSourceEquiv X Y) (structureKunnethMap X Y)

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- The proved ORIGINAL degree map, with its one degreewise inverse. -/
def structureKunnethDegreeEquiv (n : ℕ) :
    structureKunnethSum X Y n ≃ₗ[k] structureCohomology k (X ⊗ Y) n :=
  LinearEquiv.ofBijective (structureKunnethMap X Y n) (structureKunnethMap_bijective X Y n)

/-- Its forward map is literally the original degreewise operator. -/
theorem structureKunnethDegreeEquiv_toLinearMap (n : ℕ) :
    (structureKunnethDegreeEquiv X Y n).toLinearMap = structureKunnethMap X Y n := rfl

/-- The complete shared construction uses exactly the original inverse family and fibers. -/
def structureExternalLinearEquiv :
    (structureCohomologyAlgebra X ⊗[k] structureCohomologyAlgebra Y) ≃ₗ[k]
      structureCohomologyAlgebra (X ⊗ Y) :=
  DirectSum.equivAfterEquiv (structureTensorTotalSourceEquiv X Y)
    (structureKunnethDegreeEquiv X Y)

/-- The whole forward operator remains the original total Kunneth map. -/
theorem structureExternalLinearEquiv_toLinearMap :
    (structureExternalLinearEquiv X Y).toLinearMap = structureExternalLinearMap X Y := by
  exact DirectSum.equivAfterEquiv_toLinearMap_of
    (structureTensorTotalSourceEquiv X Y) (structureKunnethDegreeEquiv X Y)
    (structureKunnethMap X Y) (structureKunnethDegreeEquiv_toLinearMap X Y)

end AlgebraicGeometry.Scheme.Cohomology
