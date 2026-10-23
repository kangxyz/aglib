/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceCohomology

/-! # Coefficient naturality of the original chart comparison -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u w₁ w₂ w₃

namespace CategoryTheory.Sheaf

private theorem map_natTrans {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology D} [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{w₃} (Sheaf J AddCommGrpCat.{u + 1})]
    {R T : C ⥤ Sheaf J AddCommGrpCat.{u + 1}} (τ : R ⟶ T)
    {F G : C} (g : F ⟶ G) (q : ℕ) (x : H (R.obj F) q) :
    H.map (τ.app G) q (H.map (R.map g) q x) =
      H.map (T.map g) q (H.map (τ.app F) q x) := by
  have h := congrArg (fun k => H.map k q x) (τ.naturality g)
  simpa only [H.map_comp_apply] using h

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)
  [HasExt.{w₁} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₂} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})]
  [hChartExt : HasExt.{w₃} (AbelianSheaf.{u, u + 1} U.left)]

local instance : HasExt.{w₃}
    (Sheaf ((𝟭 Scheme.{u}).obj U.left).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hChartExt

omit [HasExt.{w₁} (AbelianSheaf.{u, u + 1} X)] in
/-- The exact slice-site comparison respects original coefficient morphisms. -/
theorem etaleSliceCohomologyEquiv_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{w₂} (F.over U) q) :
    etaleSliceCohomologyEquiv U G q
        (Sheaf.H.map (((Scheme.smallEtaleTopology X).overPullback
          AddCommGrpCat.{u + 1} U).map g) q x) =
      Sheaf.H.map ((etaleRestriction U.hom).map g) q
        (etaleSliceCohomologyEquiv U F q x) :=
  (etaleSliceSheafEquivalence U).toAdjunction.sourceExtComparison_naturality
    ((etaleSliceConstantIso U).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (((Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U).map g) q x

/-- The original chart comparison respects the actual inverse-image coefficient map. -/
theorem originalCohomologyChartEquiv_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w₁, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q U) :
    originalCohomologyChartEquiv U G q
        (((Sheaf.LargeCohomology.presheafFunctor
          (Scheme.smallEtaleTopology X) q).map g).app (op U) x) =
      Sheaf.H.map ((inverseImage U.hom).map g) q
        (originalCohomologyChartEquiv U F q x) := by
  let z := Sheaf.SliceCohomology.sliceComparison.{w₁, w₂, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U F q x
  have hs := Sheaf.SliceCohomology.sliceComparison_naturality.{w₁, w₂, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U g q x
  have he := etaleSliceCohomologyEquiv_naturality U g q z
  have hc := (congrArg (etaleSliceCohomologyEquiv U G q) hs).trans he
  have ht := congrArg (Sheaf.H.map ((inverseImageEtaleIso U.hom).inv.app G) q) hc
  exact ht.trans (Sheaf.map_natTrans (inverseImageEtaleIso U.hom).inv g q
    (etaleSliceCohomologyEquiv U F q z))

end AlgebraicGeometry.Scheme.EtaleCohomology
