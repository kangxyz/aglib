/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientComparison

/-! # Naturality of the original coefficient-colimit comparison

Both changes of the coefficient diagram and changes of its indexing category
use the native colimit maps. No continuity or invertibility hypothesis is needed.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Sheaf.H

open Limits

universe u v w e uI vI uK vK

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  {I : Type uI} [Category.{vI} I]

/-- The canonical comparison is natural in the original coefficient diagram. -/
@[reassoc]
lemma coefficientColimitComparison_naturality
    [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{w})]
    [HasColimitsOfShape I AddCommGrpCat.{e}]
    {G G' : I ⥤ Sheaf J AddCommGrpCat.{w}} (α : G ⟶ G') (n : ℕ) :
    colim.map (Functor.whiskerRight α (functorH J n)) ≫
        coefficientColimitComparison G' n =
      coefficientColimitComparison G n ≫ (functorH J n).map (colim.map α) := by
  apply colimit.hom_ext
  intro i
  dsimp only [coefficientColimitComparison]
  rw [colimit.ι_map_assoc, colimit.ι_post, colimit.ι_post_assoc]
  change (functorH J n).map (α.app i) ≫ (functorH J n).map (colimit.ι G' i) =
    (functorH J n).map (colimit.ι G i) ≫ (functorH J n).map (colim.map α)
  simpa only [Functor.map_comp] using
    (functorH J n).congr_map (colimit.ι_map α i).symm

/-- Reindexing commutes with the comparison through the original colimit transition. -/
@[reassoc]
lemma coefficientColimitComparison_reindex
    {K : Type uK} [Category.{vK} K] (E : K ⥤ I)
    (G : I ⥤ Sheaf J AddCommGrpCat.{w}) (n : ℕ)
    [HasColimit G] [HasColimit (E ⋙ G)] [HasColimit (G ⋙ functorH J n)]
    [h : HasColimit ((E ⋙ G) ⋙ functorH J n)] :
    have : HasColimit (E ⋙ G ⋙ functorH J n) := h
    coefficientColimitComparison (E ⋙ G) n ≫ (functorH J n).map (colimit.pre G E) =
      colimit.pre (G ⋙ functorH J n) E ≫ coefficientColimitComparison G n := by
  let : HasColimit (E ⋙ G ⋙ functorH J n) := h
  exact colimit.pre_post E G (functorH J n)

end CategoryTheory.Sheaf.H
