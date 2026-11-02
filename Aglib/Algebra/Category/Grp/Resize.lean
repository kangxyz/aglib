/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ShrinkYoneda

/-! # Group-only resizing of additive diagrams

The objects and additive maps use the original native Shrink realization.
Functoriality is inherited from the native type-valued shrink through faithful
forgetfulness. Component additive equivalences may compare different universes.
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe r e e' uI vI uJ vJ

variable {I : Type uI} [Category.{vI} I]

/-- Resize only the groups, retaining the native Shrink operations and original maps. -/
def resizeAdditiveDiagram (F : I ⥤ AddCommGrpCat.{e}) [h : ∀ i, Small.{r} (F.obj i)] :
    I ⥤ AddCommGrpCat.{r} :=
  Functor.Faithful.div
    (@FunctorToTypes.shrink.{r} I _ (F ⋙ forget AddCommGrpCat.{e})
      (fun i => h i))
    (forget AddCommGrpCat.{r})
    (fun i => AddCommGrpCat.of (Shrink.{r} (F.obj i)))
    (fun _ => rfl)
    (fun a => AddCommGrpCat.ofHom
      (Shrink.addEquiv.symm.toAddMonoidHom.comp
        ((F.map a).hom.comp Shrink.addEquiv.toAddMonoidHom)))
    (by intros; rfl)

/-- The resized map is the literal conjugate of the original additive map. -/
lemma resizeAdditiveDiagram_map_apply
    (F : I ⥤ AddCommGrpCat.{e}) [∀ i, Small.{r} (F.obj i)]
    {i j : I} (a : i ⟶ j) (x : Shrink.{r} (F.obj i)) :
    (resizeAdditiveDiagram.{r} F).map a x =
      Shrink.addEquiv.symm (F.map a (Shrink.addEquiv x)) := rfl

/-- Resizing preserves the value of the original map on an original group element. -/
lemma resizeAdditiveDiagram_map_shrink_symm
    (F : I ⥤ AddCommGrpCat.{e}) [∀ i, Small.{r} (F.obj i)]
    {i j : I} (a : i ⟶ j) (x : F.obj i) :
    (resizeAdditiveDiagram.{r} F).map a (Shrink.addEquiv.symm x) =
      Shrink.addEquiv.symm (F.map a x) := by
  rw [resizeAdditiveDiagram_map_apply, AddEquiv.apply_symm_apply]

/-- Actual component additive equivalences induce a resized whole-diagram isomorphism.
The original group universes are independent. -/
def resizeAdditiveDiagramIsoOfAddEquiv
    {F : I ⥤ AddCommGrpCat.{e}} {G : I ⥤ AddCommGrpCat.{e'}}
    [∀ i, Small.{r} (F.obj i)] [∀ i, Small.{r} (G.obj i)]
    (α : ∀ i, F.obj i ≃+ G.obj i)
    (naturality : ∀ {i j : I} (a : i ⟶ j) (x : F.obj i),
      α j (F.map a x) = G.map a (α i x)) :
    resizeAdditiveDiagram.{r} F ≅ resizeAdditiveDiagram.{r} G :=
  NatIso.ofComponents (fun i =>
    (((Shrink.addEquiv : Shrink.{r} (F.obj i) ≃+ F.obj i).trans (α i)).trans
      (Shrink.addEquiv : Shrink.{r} (G.obj i) ≃+ G.obj i).symm).toAddCommGrpIso) (by
    intro i j a
    apply ConcreteCategory.ext_apply
    intro x
    change Shrink.addEquiv.symm (α j
      (Shrink.addEquiv (Shrink.addEquiv.symm (F.map a (Shrink.addEquiv x))))) =
      Shrink.addEquiv.symm (G.map a
        (Shrink.addEquiv (Shrink.addEquiv.symm (α i (Shrink.addEquiv x)))))
    simp only [AddEquiv.apply_symm_apply]
    exact congrArg Shrink.addEquiv.symm (naturality a (Shrink.addEquiv x)))

/-- An original whole-diagram isomorphism induces the same group-only resized map. -/
def resizeAdditiveDiagramIso {F G : I ⥤ AddCommGrpCat.{e}}
    [∀ i, Small.{r} (F.obj i)] [∀ i, Small.{r} (G.obj i)] (α : F ≅ G) :
    resizeAdditiveDiagram.{r} F ≅ resizeAdditiveDiagram.{r} G :=
  resizeAdditiveDiagramIsoOfAddEquiv
    (fun i => (α.app i).addCommGroupIsoToAddEquiv)
    (fun {i j} (a : i ⟶ j) (x : F.obj i) =>
      ConcreteCategory.congr_hom (α.hom.naturality a) x)

/-- Group-only resizing commutes with the actual reindexing. -/
def resizeAdditiveDiagramWhiskerIso
    {J : Type uJ} [Category.{vJ} J] (K : J ⥤ I)
    (F : I ⥤ AddCommGrpCat.{e}) [h : ∀ i, Small.{r} (F.obj i)] :
    let _ : ∀ j, Small.{r} ((K ⋙ F).obj j) := fun j => h (K.obj j)
    resizeAdditiveDiagram.{r} (K ⋙ F) ≅ K ⋙ resizeAdditiveDiagram.{r} F :=
  Iso.refl _

/-- Use one canonical smallness family throughout a whole reindexed comparison. -/
def resizeAdditiveReindexIso
    {J : Type uJ} [Category.{vJ} J]
    (K : I ⥤ J) (F : I ⥤ AddCommGrpCat.{e}) (G : J ⥤ AddCommGrpCat.{e})
    (H : J ⥤ AddCommGrpCat.{r})
    [∀ i, Small.{r} (F.obj i)] [hG : ∀ j, Small.{r} (G.obj j)]
    (α : F ≅ K ⋙ G) (β : resizeAdditiveDiagram.{r} G ≅ H) :
    resizeAdditiveDiagram.{r} F ≅ K ⋙ H := by
  let : ∀ i, Small.{r} ((K ⋙ G).obj i) := fun i => hG (K.obj i)
  exact resizeAdditiveDiagramIso α ≪≫ resizeAdditiveDiagramWhiskerIso K G ≪≫
    Functor.isoWhiskerLeft K β

end CategoryTheory
