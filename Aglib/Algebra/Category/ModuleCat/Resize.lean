/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.Grp.Resize
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Shrink

/-! # Linear enhancement of the original group-only resizing

The objects use the existing native `Shrink` module and the maps use its
canonical linear equivalence. Forgetting the coefficient action gives the
existing group-only resized diagram on those exact same carriers.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat

universe r l e uI vI

variable {I : Type uI} [Category.{vI} I] (Λ : Type l) [Ring Λ]

/-- Resize only the values, using the original native `Shrink` module action. -/
def resizeDiagram (F : I ⥤ ModuleCat.{e} Λ) [h : ∀ i, Small.{r} (F.obj i)] :
    I ⥤ ModuleCat.{r} Λ :=
  Functor.Faithful.div
    (@FunctorToTypes.shrink.{r} I _ (F ⋙ forget (ModuleCat.{e} Λ)) (fun i => h i))
    (forget (ModuleCat.{r} Λ))
    (fun i => ModuleCat.of Λ (Shrink.{r} (F.obj i)))
    (fun _ => rfl)
    (fun a => ModuleCat.ofHom
      ((Shrink.linearEquiv Λ _).symm.toLinearMap.comp
        ((F.map a).hom.comp (Shrink.linearEquiv Λ _).toLinearMap)))
    (by intros; rfl)

/-- The resized restriction is exactly the conjugate of the original map. -/
@[simp]
theorem resizeDiagram_map_apply (F : I ⥤ ModuleCat.{e} Λ)
    [∀ i, Small.{r} (F.obj i)] {i j : I} (a : i ⟶ j)
    (x : Shrink.{r} (F.obj i)) :
    (resizeDiagram.{r} Λ F).map a x =
      (Shrink.linearEquiv Λ _).symm (F.map a (Shrink.linearEquiv Λ _ x)) := rfl

/-- Forgetting the linear enhancement returns the same existing additive diagram. -/
def resizeDiagramUnderlyingIso (F : I ⥤ ModuleCat.{e} Λ)
    [h : ∀ i, Small.{r} (F.obj i)] :
    resizeDiagram.{r} Λ F ⋙ forget₂ (ModuleCat.{r} Λ) AddCommGrpCat.{r} ≅
      @CategoryTheory.resizeAdditiveDiagram.{r} _ _
        (F ⋙ forget₂ (ModuleCat.{e} Λ) AddCommGrpCat.{e}) (fun i => h i) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro i j a
    ext x
    rfl)

/-- An original coefficient-linear natural transformation induces the same
canonical conjugate on the native resized values. -/
def resizeDiagramNatTrans {F G : I ⥤ ModuleCat.{e} Λ}
    [∀ i, Small.{r} (F.obj i)] [∀ i, Small.{r} (G.obj i)] (α : F ⟶ G) :
    resizeDiagram.{r} Λ F ⟶ resizeDiagram.{r} Λ G where
  app i := ModuleCat.ofHom
    ((Shrink.linearEquiv Λ _).symm.toLinearMap.comp
      ((α.app i).hom.comp (Shrink.linearEquiv Λ _).toLinearMap))
  naturality i j a := by
    ext x
    change (Shrink.linearEquiv Λ _).symm
        (α.app j (Shrink.linearEquiv Λ _
          ((Shrink.linearEquiv Λ _).symm (F.map a (Shrink.linearEquiv Λ _ x))))) =
      (Shrink.linearEquiv Λ _).symm
        (G.map a (Shrink.linearEquiv Λ _
          ((Shrink.linearEquiv Λ _).symm (α.app i (Shrink.linearEquiv Λ _ x)))))
    simp only [LinearEquiv.apply_symm_apply]
    exact congrArg (Shrink.linearEquiv Λ _).symm
      (ConcreteCategory.congr_hom (α.naturality a) (Shrink.linearEquiv Λ _ x))

end ModuleCat
