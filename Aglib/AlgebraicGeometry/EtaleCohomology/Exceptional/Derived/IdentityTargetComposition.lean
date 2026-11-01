/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.IdentityTargetComposition
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Normalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenTargetModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImageTargetModels

/-! # The original open normalization retains the original outer-adjoint map -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dU dR dT
variable (Λ : Type (u + 1)) [Ring Λ] {U X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j]
  (hU : HasDerivedCategory.{dU} (ModuleSheaf U Λ))
  (hR : HasDerivedCategory.{dR} (ModuleSheaf X Λ))
  (hT : HasDerivedCategory.{dT} (ModuleSheaf X Λ))

/-- The actual derived direct image of the identity is canonical model transport. -/
abbrev moduleDerivedDirectImageModelIdIso :=
  rightDerivedFunctorPlusIdentityModelIso hR hT (moduleDirectImage (𝟙 X) Λ)
    (moduleDirectImageIdIso Λ X)

/-- The original open contraction, not a replacement map, is target-model transport. -/
theorem moduleDerivedOpenNormalizationIso_target :
    moduleDerivedOpenNormalizationIso j Λ hU hT hR =
      isoWhiskerLeft (@rightDerivedFunctorPlus _ _ _ _ _ _ hU hR (moduleLowerShriek j Λ) _ _)
        (moduleDerivedDirectImageModelIdIso Λ hR hT) ≪≫
      rightDerivedFunctorPlusChangeTarget hU hR hT (moduleLowerShriek j Λ) := by
  have h := rightDerivedFunctorPlus_identityTargetComposition hU hR hT
    (moduleLowerShriek j Λ) (moduleDirectImage (𝟙 X) Λ) (moduleDirectImageIdIso Λ X)
  simpa only [moduleDerivedOpenNormalizationIso,
    derivedCompositeNormalizeOfPreservesHomology, rightDerivedFunctorPlusExactCompIsoModel,
    moduleDerivedDirectImageModelIdIso, Iso.trans_assoc, Iso.symm_self_id_assoc] using
    (congrArg (fun z =>
      (rightDerivedFunctorPlusExactCompIsoModel hU hR hT
        (moduleLowerShriek j Λ) (moduleDirectImage (𝟙 X) Λ)).symm ≪≫ z) h).symm

omit [IsOpenImmersion j] in
/-- The original direct-image over-identity contraction is the same target-model transport. -/
theorem moduleDerivedDirectImageOverIso_identity_target :
    @moduleDerivedDirectImageOverIso Λ _ X U X hT hU hR
        j (𝟙 X) j (Category.comp_id j) =
      isoWhiskerLeft (@rightDerivedFunctorPlus _ _ _ _ _ _ hU hR (moduleDirectImage j Λ) _ _)
        (moduleDerivedDirectImageModelIdIso Λ hR hT) ≪≫
      rightDerivedFunctorPlusChangeTarget hU hR hT (moduleDirectImage j Λ) := by
  let := hU
  let := hR
  let := hT
  have hp := congrArg (fun z : moduleDirectImage (j ≫ 𝟙 X) Λ ≅ moduleDirectImage j Λ =>
    (moduleDirectImage (j ≫ 𝟙 X) Λ).rightDerivedFunctorPlusIso z)
    (moduleDirectImageCompIso_id_comp Λ j)
  simp only [rightDerivedFunctorPlusIso_trans, rightDerivedFunctorPlusIso_eqToIso] at hp
  have h := rightDerivedFunctorPlus_identityTargetComposition hU hR hT
    (moduleDirectImage j Λ) (moduleDirectImage (𝟙 X) Λ) (moduleDirectImageIdIso Λ X)
  simp only [moduleDerivedDirectImageOverIso, moduleDerivedDirectImageCompIso,
    Iso.trans_symm, Iso.trans_assoc]
  rw [← hp]
  simp only [Iso.symm_self_id_assoc]
  simpa only [rightDerivedFunctorPlusExactCompIsoModel,
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_eq_ofPreservesInjectives,
    rightDerivedFunctorPlusIso_trans,
    moduleDerivedDirectImageModelIdIso, Iso.trans_assoc, Iso.symm_self_id_assoc] using
    (congrArg (fun z =>
      (rightDerivedFunctorPlusExactCompIsoModel hU hR hT
        (moduleDirectImage j Λ) (moduleDirectImage (𝟙 X) Λ)).symm ≪≫ z) h).symm

/-- The actual open normalization preserves the same canonical outer-adjoint map. -/
theorem moduleDerivedOpenNormalizationIso_toDirectImage :
    TargetComparisonEquation (moduleDerivedOpenNormalizationIso j Λ hU hT hR).hom
      (@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hT)
      (whiskerRight (@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hR)
          (@rightDerivedFunctorPlus _ _ _ _ _ _ hR hT (moduleDirectImage (𝟙 X) Λ) _ _) ≫
        (@moduleDerivedDirectImageOverIso Λ _ X U X hT hU hR
          j (𝟙 X) j (Category.comp_id j)).hom) := by
  change _ = _
  rw [moduleDerivedOpenNormalizationIso_target,
    moduleDerivedDirectImageOverIso_identity_target]
  have h := moduleDerivedLowerShriekToDirectImage_target Λ j hU hR hT
  change _ = _ at h
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, Category.assoc]
  rw [← h]
  simp only [← Category.assoc]
  apply congrArg (fun z => z ≫
    (rightDerivedFunctorPlusChangeTarget hU hR hT (moduleDirectImage j Λ)).hom)
  apply NatTrans.ext
  funext K
  exact ((moduleDerivedDirectImageModelIdIso Λ hR hT).hom.naturality
    ((@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hR).app K)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
