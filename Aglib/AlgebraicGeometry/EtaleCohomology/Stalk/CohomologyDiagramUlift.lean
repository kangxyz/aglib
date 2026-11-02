/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResizeCohomologyDiagram
public import Aglib.Algebra.Category.Grp.Resize.Diagram
public import Mathlib.Algebra.Category.Grp.Ulift

/-! # Original cohomology diagrams in a common universe -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe r e uI vI uJ vJ

/-- Compare an original diagram and its group-only resize by native universe lifts. -/
def additiveDiagramResizeUliftIso
    {I : Type uI} [Category.{vI} I] (F : I ⥤ AddCommGrpCat.{e})
    [∀ i, Small.{r} (F.obj i)] :
    F ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      resizeAdditiveDiagram.{r} F ⋙ AddCommGrpCat.uliftFunctor.{e, r} :=
  CategoryTheory.additiveDiagramResizeUliftIso F

/-- Transport an unresized comparison through reindexing in a common universe. -/
def additiveReindexUliftIso
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (K : I ⥤ J) (F : I ⥤ AddCommGrpCat.{e}) (G : J ⥤ AddCommGrpCat.{e})
    (H : J ⥤ AddCommGrpCat.{r}) (α : F ≅ K ⋙ G)
    (β : G ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      H ⋙ AddCommGrpCat.uliftFunctor.{e, r}) :
    F ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      (K ⋙ H) ⋙ AddCommGrpCat.uliftFunctor.{e, r} :=
  CategoryTheory.additiveReindexUliftIso K F G H α β

section NativeCohomology
universe u w s t
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{t} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The actual original and small native presheaves agree after universe lifting. -/
def originalFibreProductUliftIso :
    originalFibreProductCohomologyPresheaf f F q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, t} ≅
      smallFibreProductCohomologyPresheaf f F q ⋙ AddCommGrpCat.uliftFunctor.{t, u + 1} :=
  additiveDiagramResizeUliftIso (originalFibreProductCohomologyPresheaf f F q) ≪≫
    Functor.isoWhiskerRight (resizeOriginalFibreProductIso f F q) _
end NativeCohomology

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
