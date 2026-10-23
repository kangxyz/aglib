/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceSheaves

/-! # Original cohomology on the actual étale chart -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)
  [HasExt.{w₁} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₂} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})]
  [hChartExt : HasExt.{w₃} (AbelianSheaf.{u, u + 1} U.left)]

local instance : HasExt.{w₃}
    (Sheaf ((𝟭 Scheme.{u}).obj U.left).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hChartExt

/-- The original slice cohomology is transported by the actual exact adjunction. -/
def etaleSliceCohomologyEquiv (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{w₂} (F.over U) q ≃+
      Sheaf.H.{w₃} ((etaleRestriction U.hom).obj F) q :=
  (etaleSliceSheafEquivalence U).toAdjunction.sourceExtComparison
    ((etaleSliceConstantIso U).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (F.over U) q

/-- Represented cohomology equals cohomology on the genuine chart scheme,
with the original scheme inverse image, not an abstract replacement sheaf. -/
def originalCohomologyChartEquiv (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.LargeCohomology.H.{w₁, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F q U ≃+
      Sheaf.H.{w₃} ((inverseImage U.hom).obj F) q :=
  (Sheaf.SliceCohomology.sliceComparison.{w₁, w₂, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) U F q).trans
    ((etaleSliceCohomologyEquiv (U := U) F q).trans
      (((Sheaf.functorH (Scheme.smallEtaleTopology U.left) q).mapIso
        ((inverseImageEtaleIso U.hom).symm.app F)).addCommGroupIsoToAddEquiv))

end AlgebraicGeometry.Scheme.EtaleCohomology
