/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.PresheafTensor
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Cech

/-!
# Tensoring the original tuple Cech resolution with arbitrary coefficients

The pointwise-image augmentation of the original tuple Cech complex has an
extra degeneracy after evaluation at each site object. Tensoring with an
arbitrary module presheaf preserves that contraction, hence its positive
exactness. No flatness or local-freeness hypothesis is required. Applying
original Hom into an injective presheaf consequently gives exact cochains.
This is an acyclicity supplier for the existing internal-Hom sheaf, not a
new cohomology or resolution model.

Sources: `SheafCohomology/Cech/CoverResolution`, the original evaluated extra
degeneracy; `ModuleCoefficients/Cech`, the actual free image augmentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex MonoidalCategory

universe c h r

namespace PresheafOfModules.Cech

variable {C : Type c} [Category.{h} C] (R : Cᵒᵖ ⥤ CommRingCat.{r})
  (M : PresheafOfModulesOfCommRing.{r} R)
  {F G : Cᵒᵖ ⥤ Type r} (f : F ⟶ G)

/-- Native presheaf right tensor is additive on its original componentwise tensor maps. -/
instance tensorRight_additive : (tensorRight M).Additive where
  map_add {X Y f g} := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    change ((f.app U).hom x + (g.app U).hom x) ⊗ₜ[R.obj U] y =
      (f.app U).hom x ⊗ₜ[R.obj U] y + (g.app U).hom x ⊗ₜ[R.obj U] y
    exact TensorProduct.add_tmul _ _ _

/-- Tensor the existing free tuple complex by the specified original module presheaf. -/
def tensorFreeComplex : ChainComplex (PresheafOfModulesOfCommRing.{r} R) ℕ :=
  ((tensorRight M).mapHomologicalComplex _).obj
    (freeComplex.{r, c, h, r} (R ⋙ forget₂ CommRingCat RingCat) f)

/-- Tensor the original augmentation to its original pointwise-image object. -/
def tensorImageAugmentation : tensorFreeComplex R M f ⟶
    ((tensorRight M).mapHomologicalComplex _).obj
      ((ChainComplex.single₀ _).obj
        ((PresheafOfModules.freeWide.{r, r, c, h} (R ⋙ forget₂ CommRingCat RingCat)).obj
          (Subfunctor.range f).toFunctor)) :=
  ((tensorRight M).mapHomologicalComplex _).map
    (freeImageAugmentation.{r, c, h, r} (R ⋙ forget₂ CommRingCat RingCat) f)

/-- The original image augmentation remains a quasi-isomorphism after arbitrary tensoring. -/
theorem tensorImageAugmentation_quasiIso : QuasiIso (tensorImageAugmentation R M f) := by
  apply (quasiIso_map_iff_of_preservesHomology (tensorImageAugmentation R M f)
    (PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat))).1
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro U
  let E := tensorRight M ⋙ PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat) ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{r}).obj U
  let X := ((SimplicialObject.Augmented.whiskering _ _).obj
    (PresheafOfModules.freeWide.{r, r, c, h} (R ⋙ forget₂ CommRingCat RingCat))).obj
      (CategoryTheory.Presheaf.Cech.imageAugmentedNerve f)
  change QuasiIso ((E.mapHomologicalComplex _).map
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app X))
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (CategoryTheory.Presheaf.Cech.mapAugmentationArrowIso E X)).2
  exact inferInstanceAs
    (QuasiIso (((CategoryTheory.Presheaf.Cech.evaluatedImageExtraDegeneracy f U).map
      (ModuleCat.freeWideFunctor.{r, r} (R.obj U) ⋙ tensorRight (M.obj U) ⋙
        forget₂ _ AddCommGrpCat)).homotopyEquiv.hom))

/-- Positive exactness of the same tensor complex, without coefficient flatness. -/
theorem tensorFreeComplex_exactAt_succ (n : ℕ) : (tensorFreeComplex R M f).ExactAt (n + 1) := by
  have := tensorImageAugmentation_quasiIso R M f
  apply (exactAt_iff_of_quasiIsoAt (tensorImageAugmentation R M f) (n + 1)).2
  exact (ChainComplex.exactAt_succ_single_obj _ n).of_iso
    ((singleMapHomologicalComplex (tensorRight M) (.down ℕ) 0).app _).symm

/-- Original Hom cochains on the tensor of the original tuple complex. -/
def tensorHomComplex (I : PresheafOfModulesOfCommRing.{r} R) :
    CochainComplex AddCommGrpCat.{max r c} ℕ :=
  ((preadditiveYoneda.obj I).mapHomologicalComplex (.up ℕ)).obj (tensorFreeComplex R M f).op

/-- An injective target gives positive exactness of the original tensor Hom cochains. -/
theorem tensorHomComplex_exactAt_succ (I : PresheafOfModulesOfCommRing.{r} R)
    [Injective I] (n : ℕ) : (tensorHomComplex R M f I).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  have hm := ((HomologicalComplex.exactAt_iff _ _).1
    (tensorFreeComplex_exactAt_succ R M f n).op).map (preadditiveYonedaObj I)
  exact hm.map (forget₂ (ModuleCat.{max r c} (End I)) AddCommGrpCat.{max r c})

end PresheafOfModules.Cech
