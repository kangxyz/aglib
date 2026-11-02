/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductPresheaf
public import Aglib.Algebra.Category.Grp.Resize

/-! # Group-only resizing of whole original cohomology diagrams -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe r e uI vI uJ vJ

variable {I : Type uI} [Category.{vI} I]

/-- Compatibility name for the canonical group-only resize. -/
abbrev resizeAdditiveDiagram (F : I ⥤ AddCommGrpCat.{e}) [∀ i, Small.{r} (F.obj i)] :
    I ⥤ AddCommGrpCat.{r} :=
  CategoryTheory.resizeAdditiveDiagram.{r} F

/-- Compatibility view of the same actual whole-diagram isomorphism. -/
abbrev resizeAdditiveDiagramIso {F G : I ⥤ AddCommGrpCat.{e}}
    [∀ i, Small.{r} (F.obj i)] [∀ i, Small.{r} (G.obj i)] (α : F ≅ G) :
    resizeAdditiveDiagram.{r} F ≅ resizeAdditiveDiagram.{r} G :=
  CategoryTheory.resizeAdditiveDiagramIso α

/-- Compatibility view of canonical group resizing under reindexing. -/
abbrev resizeAdditiveDiagramWhiskerIso
    {J : Type uJ} [Category.{vJ} J] (K : J ⥤ I)
    (F : I ⥤ AddCommGrpCat.{e}) [h : ∀ i, Small.{r} (F.obj i)] :
    let _ : ∀ j, Small.{r} ((K ⋙ F).obj j) := fun j => h (K.obj j)
    resizeAdditiveDiagram.{r} (K ⋙ F) ≅ K ⋙ resizeAdditiveDiagram.{r} F :=
  CategoryTheory.resizeAdditiveDiagramWhiskerIso K F

section NativeCohomology
universe u w s t
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{t} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- Resizing the original whole diagram recovers the actual small cohomology presheaf. -/
def resizeOriginalFibreProductIso :
    resizeAdditiveDiagram.{u + 1} (originalFibreProductCohomologyPresheaf f F q) ≅
      smallFibreProductCohomologyPresheaf f F q :=
  Iso.refl _
end NativeCohomology

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
