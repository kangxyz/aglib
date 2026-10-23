/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResizeCohomologyDiagram

/-! # Whole-diagram resizing across an original reindexing comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe r e uI vI uJ vJ

/-- Use one canonical smallness family throughout a whole reindexed comparison. -/
def resizeAdditiveReindexIso
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (K : I ⥤ J) (F : I ⥤ AddCommGrpCat.{e}) (G : J ⥤ AddCommGrpCat.{e})
    (H : J ⥤ AddCommGrpCat.{r})
    [∀ i, Small.{r} (F.obj i)] [hG : ∀ j, Small.{r} (G.obj j)]
    (α : F ≅ K ⋙ G) (β : resizeAdditiveDiagram.{r} G ≅ H) :
    resizeAdditiveDiagram.{r} F ≅ K ⋙ H := by
  let : ∀ i, Small.{r} ((K ⋙ G).obj i) := fun i => hG (K.obj i)
  exact resizeAdditiveDiagramIso α ≪≫ resizeAdditiveDiagramWhiskerIso K G ≪≫
    Functor.isoWhiskerLeft K β

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
