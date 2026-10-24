/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.AcyclicColimit
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject

/-!
# Actual filtered unions of acyclic subobjects

The supremum subobject carries its canonical cocone on the entire filtered
diagram. Native Grothendieck subobject theory supplies its colimit universal
property, and the existing acyclic-colimit theorem supplies acyclicity.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {M : C} {J : Type w} [SmallCategory J] (F : J ⥤ MonoOver M)

/-- The supremum of the subobjects in the entire diagram. -/
def diagramSup : Subobject M := ⨆ j, Subobject.mk (F.obj j).obj.hom

lemma le_diagramSup (j : J) : Subobject.mk (F.obj j).obj.hom ≤ diagramSup F :=
  le_iSup (fun k ↦ Subobject.mk (F.obj k).obj.hom) j

/-- The canonical cocone in the over category, retaining every diagram map. -/
def diagramSupCocone : Cocone (F ⋙ MonoOver.forget M) where
  pt := Over.mk (diagramSup F).arrow
  ι :=
    { app j := Over.homMk (U := (F.obj j).obj) (V := Over.mk (diagramSup F).arrow)
        (Subobject.ofMkLE (F.obj j).obj.hom (diagramSup F)
          (le_diagramSup F j))
        (Subobject.ofMkLE_arrow _)
      naturality j k f := by
        apply Over.OverMorphism.ext
        apply (cancel_mono (diagramSup F).arrow).1
        change ((F.map f).hom.left ≫
            Subobject.ofMkLE (F.obj k).obj.hom (diagramSup F) _) ≫ (diagramSup F).arrow =
          (Subobject.ofMkLE (F.obj j).obj.hom (diagramSup F) _ ≫ 𝟙 _) ≫ (diagramSup F).arrow
        rw [Category.comp_id, Category.assoc, Subobject.ofMkLE_arrow,
          Subobject.ofMkLE_arrow]
        exact MonoOver.w (F.map f) }

/-- The actual supremum cocone is a colimit, not merely an upper bound. -/
def diagramSupIsColimit [IsFiltered J] :
    IsColimit ((Over.forget M).mapCocone (diagramSupCocone F)) := by
  have : Mono (diagramSupCocone F).pt.hom :=
    inferInstanceAs (Mono (diagramSup F).arrow)
  apply isColimitMapCoconeOfSubobjectMkEqISup F (diagramSupCocone F)
  change Subobject.mk (diagramSup F).arrow = diagramSup F
  exact Subobject.mk_arrow _

end CategoryTheory.IsGrothendieckAbelian

namespace CochainComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {M : CochainComplex C ℤ} {J : Type w} [SmallCategory J] [IsFiltered J]

/-- A filtered union of acyclic native subcomplexes is acyclic. The same
supremum has the explicit full-diagram colimit cocone `diagramSupIsColimit`. -/
lemma diagramSup_acyclic (F : J ⥤ MonoOver M)
    (hF : ∀ j, (F.obj j).obj.left.Acyclic) :
    (diagramSup F : CochainComplex C ℤ).Acyclic := by
  let D := F ⋙ MonoOver.forget M ⋙ Over.forget M
  have hD : (colimit D).Acyclic := HomologicalComplex.acyclic_colimit D hF
  let e : colimit D ≅ (diagramSup F : CochainComplex C ℤ) :=
    (colimit.isColimit D).coconePointUniqueUpToIso (diagramSupIsColimit F)
  intro n
  exact (hD n).of_iso e

end CochainComplex
