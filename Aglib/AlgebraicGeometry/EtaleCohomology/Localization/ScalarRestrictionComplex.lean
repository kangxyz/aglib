/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleComplex
public import Aglib.Algebra.Homology.CochainComplexPlus.Single
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionExact

/-! # Scalar restriction of the original localization sequence of complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The original first-vertex comparisons assembled before passing to components. -/
def moduleLocalizationScalarRestrictionFirstNatIso :
    (moduleInverseImage j Γ ⋙ moduleLowerShriek j Γ) ⋙ moduleRestrictScalars X φ ≅
      moduleRestrictScalars X φ ⋙ (moduleInverseImage j Λ ⋙ moduleLowerShriek j Λ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleLowerShriekScalarRestrictionIso j φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleInverseImageScalarRestrictionIso j φ) _ ≪≫
    Functor.associator _ _ _

/-- The original third-vertex comparisons assembled before passing to components. -/
def moduleLocalizationScalarRestrictionThirdNatIso :
    (moduleInverseImage i Γ ⋙ moduleDirectImage i Γ) ⋙ moduleRestrictScalars X φ ≅
      moduleRestrictScalars X φ ⋙ (moduleInverseImage i Λ ⋙ moduleDirectImage i Λ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleDirectImageScalarRestrictionIso i φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleInverseImageScalarRestrictionIso i φ) _ ≪≫
    Functor.associator _ _ _

/-- Termwise restriction identifies the actual localization short complexes,
with the original counit and unit in every degree. -/
def moduleLocalizationComplexScalarRestrictionIso
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (K : CochainComplex.Plus (ModuleSheaf X Γ)) :
    (moduleLocalizationComplex j Γ i hcomp K).map
        (moduleRestrictScalars X φ).mapCochainComplexPlus ≅
      moduleLocalizationComplex j Λ i hcomp
        ((moduleRestrictScalars X φ).mapCochainComplexPlus.obj K) := by
  refine ShortComplex.isoMk
    ((NatIso.mapCochainComplexPlus
      (moduleLocalizationScalarRestrictionFirstNatIso j φ)).app K)
    (Iso.refl _)
    ((NatIso.mapCochainComplexPlus
      (moduleLocalizationScalarRestrictionThirdNatIso i φ)).app K) ?_ ?_
  · apply ObjectProperty.hom_ext
    ext n : 1
    change (moduleLocalizationScalarRestrictionFirstNatIso j φ).hom.app (K.obj.X n) ≫
      (moduleLowerShriekAdjunction j Λ).counit.app
        ((moduleRestrictScalars X φ).obj (K.obj.X n)) =
      (moduleRestrictScalars X φ).map
        ((moduleLowerShriekAdjunction j Γ).counit.app (K.obj.X n)) ≫ 𝟙 _
    simp only [moduleLocalizationScalarRestrictionFirstNatIso,
      Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    have h := moduleLocalizationScalarRestriction_counit j φ (K.obj.X n)
    change ((moduleLowerShriekScalarRestrictionIso j φ).hom.app
      ((moduleInverseImage j Γ).obj (K.obj.X n)) ≫
        (moduleLowerShriek j Λ).map
          ((moduleInverseImageScalarRestrictionIso j φ).hom.app (K.obj.X n))) ≫
      (moduleLowerShriekAdjunction j Λ).counit.app
        ((moduleRestrictScalars X φ).obj (K.obj.X n)) = _ at h
    exact h
  · apply ObjectProperty.hom_ext
    ext n : 1
    change 𝟙 _ ≫ (moduleInverseImageAdjunction i Λ).unit.app
      ((moduleRestrictScalars X φ).obj (K.obj.X n)) =
      (moduleRestrictScalars X φ).map
        ((moduleInverseImageAdjunction i Γ).unit.app (K.obj.X n)) ≫
          (moduleLocalizationScalarRestrictionThirdNatIso i φ).hom.app (K.obj.X n)
    simp only [moduleLocalizationScalarRestrictionThirdNatIso,
      Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    have h := moduleLocalizationScalarRestriction_unit i φ (K.obj.X n)
    change (moduleRestrictScalars X φ).map
      ((moduleInverseImageAdjunction i Γ).unit.app (K.obj.X n)) ≫
        ((moduleDirectImageScalarRestrictionIso i φ).hom.app
          ((moduleInverseImage i Γ).obj (K.obj.X n)) ≫
            (moduleDirectImage i Λ).map
              ((moduleInverseImageScalarRestrictionIso i φ).hom.app (K.obj.X n))) = _ at h
    exact h.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
