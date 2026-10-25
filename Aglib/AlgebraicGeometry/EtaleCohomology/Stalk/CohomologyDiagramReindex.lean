/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.CohomologyDiagramUlift

/-! # Two-step native stalk indexing in a common universe -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe r e uI vI uJ vJ uK vK

/-- Preserve the original right-associated two-step stalk indexing throughout transport. -/
def additiveTwiceReindexUliftIso
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    {K : Type uK} [Category.{vK} K]
    (A : I ⥤ J) (B : J ⥤ K)
    (F : I ⥤ AddCommGrpCat.{e}) (G : K ⥤ AddCommGrpCat.{e})
    (H : K ⥤ AddCommGrpCat.{r}) (α : F ≅ A ⋙ B ⋙ G)
    (β : G ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      H ⋙ AddCommGrpCat.uliftFunctor.{e, r}) :
    F ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      (A ⋙ B ⋙ H) ⋙ AddCommGrpCat.uliftFunctor.{e, r} :=
  additiveReindexUliftIso A F (B ⋙ G) (B ⋙ H) α
    (additiveReindexUliftIso B (B ⋙ G) G H (Iso.refl _) β)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
