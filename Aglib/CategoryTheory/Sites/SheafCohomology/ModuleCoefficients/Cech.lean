/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoverResolution
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.PresheafInjective
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Free
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Free module Cech resolutions

The original tuple nerve is resolved over the original presheaf of rings.
Its augmentation is to the pointwise image, not to the target presheaf.
The positive exactness below therefore needs no surjectivity assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace PresheafOfModules.Cech

universe r c h m

variable {C : Type c} [Category.{h} C] (R : Cᵒᵖ ⥤ RingCat.{r})
    {F G : Cᵒᵖ ⥤ Type (max r m)} (f : F ⟶ G)

/-- The free module complex on the original tuple Cech nerve. -/
def freeComplex : ChainComplex (PresheafOfModules.{max r m} R) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    (((SimplicialObject.whiskering _ _).obj (PresheafOfModules.freeWide.{r, m, c, h} R)).obj
      (CategoryTheory.Presheaf.Cech.nerve f))

/-- The augmentation to the free modules on the pointwise image. -/
def freeImageAugmentation : freeComplex.{r, c, h, m} R f ⟶
    (ChainComplex.single₀ _).obj
      ((PresheafOfModules.freeWide.{r, m, c, h} R).obj (Subfunctor.range f).toFunctor) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering _ _).obj
      (PresheafOfModules.freeWide.{r, m, c, h} R)).obj
      (CategoryTheory.Presheaf.Cech.imageAugmentedNerve f))

/-- The free module image augmentation is a quasi-isomorphism. -/
theorem freeImageAugmentation_quasiIso : QuasiIso (freeImageAugmentation.{r, c, h, m} R f) := by
  apply (quasiIso_map_iff_of_preservesHomology
    (freeImageAugmentation.{r, c, h, m} R f) (PresheafOfModules.toPresheaf R)).1
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro U
  let E := PresheafOfModules.toPresheaf R ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{max r m}).obj U
  let X := ((SimplicialObject.Augmented.whiskering _ _).obj
    (PresheafOfModules.freeWide.{r, m, c, h} R)).obj
      (CategoryTheory.Presheaf.Cech.imageAugmentedNerve f)
  change QuasiIso ((E.mapHomologicalComplex _).map
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app X))
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (CategoryTheory.Presheaf.Cech.mapAugmentationArrowIso E X)).2
  exact inferInstanceAs
    (QuasiIso (((CategoryTheory.Presheaf.Cech.evaluatedImageExtraDegeneracy f U).map
      (ModuleCat.freeWideFunctor.{r, max r m} (R.obj U) ⋙
        forget₂ _ AddCommGrpCat)).homotopyEquiv.hom))

/-- Positive exactness of the free module Cech complex. -/
theorem freeComplex_exactAt_succ (n : ℕ) : (freeComplex.{r, c, h, m} R f).ExactAt (n + 1) := by
  have := freeImageAugmentation_quasiIso.{r, c, h, m} R f
  exact (exactAt_iff_of_quasiIsoAt (freeImageAugmentation.{r, c, h, m} R f) (n + 1)).2
    (ChainComplex.exactAt_succ_single_obj _ n)

/-- Module-linear Cech cochains with values in a module presheaf. -/
def homComplex (I : PresheafOfModules.{max r m} R) :
    CochainComplex AddCommGrpCat.{max r m c} ℕ :=
  ((preadditiveYoneda.obj I).mapHomologicalComplex (.up ℕ)).obj (freeComplex.{r, c, h, m} R f).op

/-- Genuine positive Cech exactness for injective module presheaves. -/
theorem homComplex_exactAt_succ (I : PresheafOfModules.{max r m} R) [Injective I] (n : ℕ) :
    (homComplex.{r, c, h, m} R f I).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  have hm := ((HomologicalComplex.exactAt_iff _ _).1
    (freeComplex_exactAt_succ.{r, c, h, m} R f n).op).map (preadditiveYonedaObj I)
  exact hm.map (forget₂ (ModuleCat.{max r m c} (End I)) AddCommGrpCat.{max r m c})

end PresheafOfModules.Cech
