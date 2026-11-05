/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Resize
public import Aglib.Algebra.Category.Grp.ResizeNaturality
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Functoriality of the original module resizing

The existing native `Shrink` modules and conjugate maps form a coefficient
functor. Its identity, composition, additive and scalar laws are proved here,
with independent ring, value, index and coefficient universes. Forgetting the
module structure recovers the existing additive resizing, naturally in the
original coefficient. No geometric hypotheses or alternate carriers are used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat

universe r l e uI vI uC vC

variable {I : Type uI} [Category.{vI} I]
  {C : Type uC} [Category.{vC} C]

section Ring

variable (Λ : Type l) [Ring Λ]

/-- The original resized transformation is its canonical linear conjugate. -/
@[simp]
theorem resizeDiagramNatTrans_app_apply {P Q : I ⥤ ModuleCat.{e} Λ}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    (a : P ⟶ Q) (i : I) (x : Shrink.{r} (P.obj i)) :
    (resizeDiagramNatTrans.{r} Λ a).app i x =
      (Shrink.linearEquiv Λ _).symm (a.app i (Shrink.linearEquiv Λ _ x)) := rfl

/-- Resizing preserves the original identity transformation. -/
theorem resizeDiagramNatTrans_id (P : I ⥤ ModuleCat.{e} Λ)
    [∀ i, Small.{r} (P.obj i)] :
    resizeDiagramNatTrans.{r} Λ (𝟙 P) = 𝟙 (resizeDiagram.{r} Λ P) := by
  ext i x
  change (Shrink.linearEquiv Λ _).symm (Shrink.linearEquiv Λ _ x) = x
  exact LinearEquiv.symm_apply_apply _ _

/-- Resizing preserves composition of the original transformations. -/
theorem resizeDiagramNatTrans_comp {P Q T : I ⥤ ModuleCat.{e} Λ}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    [∀ i, Small.{r} (T.obj i)] (a : P ⟶ Q) (b : Q ⟶ T) :
    resizeDiagramNatTrans.{r} Λ (a ≫ b) =
      resizeDiagramNatTrans.{r} Λ a ≫ resizeDiagramNatTrans.{r} Λ b := by
  ext i x
  change (Shrink.linearEquiv Λ _).symm (b.app i (a.app i (Shrink.linearEquiv Λ _ x))) =
    (Shrink.linearEquiv Λ _).symm (b.app i (Shrink.linearEquiv Λ _
      ((Shrink.linearEquiv Λ _).symm (a.app i (Shrink.linearEquiv Λ _ x)))))
  rw [LinearEquiv.apply_symm_apply]

/-- Resizing is additive on the actual maps of diagrams. -/
theorem resizeDiagramNatTrans_add {P Q : I ⥤ ModuleCat.{e} Λ}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)] (a b : P ⟶ Q) :
    resizeDiagramNatTrans.{r} Λ (a + b) =
      resizeDiagramNatTrans.{r} Λ a + resizeDiagramNatTrans.{r} Λ b := by
  ext i x
  change (Shrink.linearEquiv Λ _).symm
    (a.app i (Shrink.linearEquiv Λ _ x) + b.app i (Shrink.linearEquiv Λ _ x)) = _
  exact map_add _ _ _

/-- Resize an entire coefficient functor using its original module-valued maps. -/
def resizeDiagramFunctor (P : C ⥤ I ⥤ ModuleCat.{e} Λ)
    [∀ c i, Small.{r} ((P.obj c).obj i)] : C ⥤ I ⥤ ModuleCat.{r} Λ where
  obj c := resizeDiagram.{r} Λ (P.obj c)
  map a := resizeDiagramNatTrans.{r} Λ (P.map a)
  map_id c := by rw [P.map_id, resizeDiagramNatTrans_id]
  map_comp a b := by rw [P.map_comp, resizeDiagramNatTrans_comp]

/-- An additive coefficient functor remains additive after the original resize. -/
instance resizeDiagramFunctor_additive [Preadditive C]
    (P : C ⥤ I ⥤ ModuleCat.{e} Λ) [P.Additive]
    [∀ c i, Small.{r} ((P.obj c).obj i)] :
    (resizeDiagramFunctor.{r} Λ P).Additive where
  map_add := by
    intro c d a b
    change resizeDiagramNatTrans Λ (P.map (a + b)) = _
    rw [P.map_add, resizeDiagramNatTrans_add]
    rfl

/-- Forgetting scalars recovers the same additive coefficient functor,
naturally in the original coefficients as well as the diagram index. -/
def resizeDiagramFunctorUnderlyingIso (P : C ⥤ I ⥤ ModuleCat.{e} Λ)
    [h : ∀ c i, Small.{r} ((P.obj c).obj i)] :
    resizeDiagramFunctor.{r} Λ P ⋙
        (Functor.whiskeringRight I _ _).obj
          (forget₂ (ModuleCat.{r} Λ) AddCommGrpCat.{r}) ≅
      @resizeAdditiveDiagramFunctor.{r} I _ C _
        (P ⋙ (Functor.whiskeringRight I _ _).obj
          (forget₂ (ModuleCat.{e} Λ) AddCommGrpCat.{e})) (fun c i => h c i) :=
  NatIso.ofComponents (fun c => resizeDiagramUnderlyingIso.{r} Λ (P.obj c)) (by
    intro c d a
    ext i x
    rfl)

end Ring

section CommRing

variable (Λ : Type l) [CommRing Λ]

/-- The actual conjugate maps preserve the original coefficient scalar action. -/
theorem resizeDiagramNatTrans_smul {P Q : I ⥤ ModuleCat.{e} Λ}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    (a : P ⟶ Q) (t : Λ) :
    resizeDiagramNatTrans.{r} Λ (t • a) = t • resizeDiagramNatTrans.{r} Λ a := by
  ext i x
  change (Shrink.linearEquiv Λ _).symm
    (t • a.app i (Shrink.linearEquiv Λ _ x)) = _
  exact (Shrink.linearEquiv Λ _).symm.map_smul t _

/-- A linear coefficient functor remains linear on the same resized modules. -/
instance resizeDiagramFunctor_linear [Preadditive C] [CategoryTheory.Linear Λ C]
    (P : C ⥤ I ⥤ ModuleCat.{e} Λ) [P.Linear Λ]
    [∀ c i, Small.{r} ((P.obj c).obj i)] :
    (resizeDiagramFunctor.{r} Λ P).Linear Λ where
  map_smul a t := by
    change resizeDiagramNatTrans Λ (P.map (t • a)) = _
    rw [Functor.map_smul, resizeDiagramNatTrans_smul]
    rfl

end CommRing

end ModuleCat
