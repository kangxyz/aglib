/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethComparison.Signed
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Basic
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Graded

/-!
# Whole comparison of the original signed and linear Kunneth maps

The original graded external product and the degreewise Kunneth map agree on
whole homogeneous tensor maps. The generic total-degree comparison composes
those laws before any native cohomology value is evaluated.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

/-- The original degree map after its original fiber inclusion is the original tensor map. -/
theorem structureKunnethMap_component (p q : ℕ) :
    structureKunnethMap X Y (p + q) ∘ₗ
        DirectSum.lof k (HomologicalComplex₂.TotalDegree (p + q))
          (fun s => structureCohomology k X s.val.1 ⊗[k]
            structureCohomology k Y s.val.2) ⟨(p, q), rfl⟩ =
      structureExternalTensor X Y (p := p) (q := q) rfl := by
  unfold structureKunnethMap
  apply DirectSum.toModule_comp_lof_eq

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- The one chosen inverse retains the signed map as its complete forward operator. -/
abbrev structureExternalAlgebraMap_linear :=
  let hSigned := structureExternalLinearMap_signed X Y
  let hChosen := structureExternalLinearEquiv_toLinearMap X Y
  DirectSum.ExternalSignedTotalEq.of_chosen (L := structureExternalLinearMap X Y)
    hSigned (structureExternalLinearEquiv X Y) hChosen

end AlgebraicGeometry.Scheme.Cohomology
