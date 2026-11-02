/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.Resize

/-! # Native common-universe transport of additive diagrams

The existing group-only resize and native ULift functors supply one whole
comparison. Reindexing uses the original natural isomorphisms and associators;
the original Shrink and ULift values remain literal. No index or value universe
is identified, and no new resize realization is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

universe r e uI vI uJ vJ uK vK

/-- Compare an original diagram and its group-only resize by native universe lifts. -/
def additiveDiagramResizeUliftIso
    {I : Type uI} [Category.{vI} I] (F : I ⥤ AddCommGrpCat.{e})
    [∀ i, Small.{r} (F.obj i)] :
    F ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      resizeAdditiveDiagram.{r} F ⋙ AddCommGrpCat.uliftFunctor.{e, r} :=
  NatIso.ofComponents (fun i =>
    (((AddEquiv.ulift : ULift.{r} (F.obj i) ≃+ F.obj i).trans
      (Shrink.addEquiv : Shrink.{r} (F.obj i) ≃+ F.obj i).symm).trans
      (AddEquiv.ulift : ULift.{e} (Shrink.{r} (F.obj i)) ≃+
        Shrink.{r} (F.obj i)).symm).toAddCommGrpIso) (by
    intro i j a
    apply ConcreteCategory.ext_apply
    intro x
    apply ULift.ext
    change Shrink.addEquiv.symm (F.map a x.down) =
      Shrink.addEquiv.symm (F.map a
        (Shrink.addEquiv (Shrink.addEquiv.symm x.down)))
    rw [AddEquiv.apply_symm_apply])

/-- Transport an unresized comparison through reindexing in a common universe. -/
def additiveReindexUliftIso
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (K : I ⥤ J) (F : I ⥤ AddCommGrpCat.{e}) (G : J ⥤ AddCommGrpCat.{e})
    (H : J ⥤ AddCommGrpCat.{r}) (α : F ≅ K ⋙ G)
    (β : G ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      H ⋙ AddCommGrpCat.uliftFunctor.{e, r}) :
    F ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      (K ⋙ H) ⋙ AddCommGrpCat.uliftFunctor.{e, r} :=
  Functor.isoWhiskerRight α _ ≪≫ Functor.associator K G _ ≪≫
    Functor.isoWhiskerLeft K β ≪≫ (Functor.associator K H _).symm

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

/-- The common-universe comparison retains the original two stage maps. -/
theorem additiveTwiceReindexUliftIso_apply
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    {K : Type uK} [Category.{vK} K]
    (A : I ⥤ J) (B : J ⥤ K)
    (F : I ⥤ AddCommGrpCat.{e}) (G : K ⥤ AddCommGrpCat.{e})
    (H : K ⥤ AddCommGrpCat.{r}) (α : F ≅ A ⋙ B ⋙ G)
    (β : G ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      H ⋙ AddCommGrpCat.uliftFunctor.{e, r}) (i : I) (x : F.obj i) :
    (additiveTwiceReindexUliftIso A B F G H α β).hom.app i (ULift.up x) =
      β.hom.app (B.obj (A.obj i)) (ULift.up (α.hom.app i x)) := by
  simp [additiveTwiceReindexUliftIso, additiveReindexUliftIso]
  rfl

end CategoryTheory
