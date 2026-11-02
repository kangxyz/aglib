/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenComparisonCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition
public import Aglib.CategoryTheory.Adjunction.MatePastingIdentification

/-! # Horizontal pasting of the original proper/open mate

Reflect original inverse-image square pasting through the actual open
adjunctions and original conjugate lower-shriek compositors, then take the
original proper-map mates. No desired open-square pasting is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU₀ wU₁ wU₂ wX₀ wX₁ wX₂

variable (Λ : Type (u + 1)) [Ring Λ]
  {U₀ U₁ U₂ X₀ X₁ X₂ : Scheme.{u}}
  (j₁ : U₁ ⟶ U₀) (j₂ : U₂ ⟶ U₁) (i₁ : X₁ ⟶ X₀) (i₂ : X₂ ⟶ X₁)
  (f₀ : X₀ ⟶ U₀) (f₁ : X₁ ⟶ U₁) (f₂ : X₂ ⟶ U₂)
  [Etale j₁] [Etale j₂] [Etale i₁] [Etale i₂]
  (h₁ : IsPullback f₁ i₁ j₁ f₀) (h₂ : IsPullback f₂ i₂ j₂ f₁)
  (ht : IsPullback f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀)
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]

private theorem inverse_openComparison_hComp
    (K : DerivedCategory.Plus (ModuleSheaf U₂ Λ)) :
    VerticalSquareEquation
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).inv)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).inv)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ).inv)
      (moduleDerivedLowerShriekCompIso Λ j₁ j₂)
      (moduleDerivedLowerShriekCompIso Λ i₁ i₂) K := by
  exact verticalSquareEquation_of_identified_mates
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).inv)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).inv)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ).inv)
    (moduleDerivedLowerShriekCompIso Λ j₁ j₂)
    (moduleDerivedLowerShriekCompIso Λ i₁ i₂)
    (moduleDerivedInverseImageCompIso Λ j₁ j₂)
    (moduleDerivedInverseImageCompIso Λ i₁ i₂)
    (moduleDerivedLowerShriekAdjunction j₂ Λ) (moduleDerivedLowerShriekAdjunction i₂ Λ)
    (moduleDerivedLowerShriekAdjunction j₁ Λ) (moduleDerivedLowerShriekAdjunction i₁ Λ)
    (moduleDerivedLowerShriekAdjunction (j₂ ≫ j₁) Λ)
    (moduleDerivedLowerShriekAdjunction (i₂ ≫ i₁) Λ)
    (conjugateEquiv_moduleDerivedLowerShriekCompIso_hom Λ j₁ j₂)
    (conjugateEquiv_moduleDerivedLowerShriekCompIso_hom Λ i₁ i₂)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedInverseImageSquareIso Λ f₁ f₂ j₂ i₂ h₂.w).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedInverseImageSquareIso Λ f₀ f₁ j₁ i₁ h₁.w).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedInverseImageSquareIso Λ f₀ f₂ (j₂ ≫ j₁) (i₂ ≫ i₁) ht.w).hom)
    (mateEquiv_moduleDerivedOpenComparison_inv f₂ i₂ j₂ f₁ h₂ Λ)
    (mateEquiv_moduleDerivedOpenComparison_inv f₁ i₁ j₁ f₀ h₁ Λ)
    (mateEquiv_moduleDerivedOpenComparison_inv f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ)
    (moduleDerivedInverseImageSquareIso_hComp Λ f₀ f₁ f₂ j₁ j₂ i₁ i₂
      h₁.w h₂.w ht.w) K

/-- Actual horizontal open-comparison coherence, reflected from the canonical
inverse-image squares rather than postulated for the lower-shriek maps. -/
theorem moduleDerivedOpenComparison_hComp
    (K : DerivedCategory.Plus (ModuleSheaf U₂ Λ)) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ).hom)
      (moduleDerivedLowerShriekCompIso Λ j₁ j₂).hom
      (moduleDerivedLowerShriekCompIso Λ i₁ i₂).hom K :=
  CategoryTheory.forward_horizontal_of_inverse_vertical
    (moduleDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ)
    (moduleDerivedLowerShriekCompIso Λ j₁ j₂)
    (moduleDerivedLowerShriekCompIso Λ i₁ i₂)
    (inverse_openComparison_hComp Λ j₁ j₂ i₁ i₂ f₀ f₁ f₂ h₁ h₂ ht) K

/-- Horizontal pasting of the actual global proper/open mixed mates. -/
theorem moduleProperOpenMate_hComp
    (K : DerivedCategory.Plus (ModuleSheaf X₂ Λ)) :
    HorizontalMateEquation
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ).hom)
      (moduleDerivedLowerShriekCompIso Λ j₁ j₂).hom
      (moduleDerivedLowerShriekCompIso Λ i₁ i₂).hom
      (moduleDerivedAdjunction Λ f₂) (moduleDerivedAdjunction Λ f₁)
      (moduleDerivedAdjunction Λ f₀) K :=
  horizontalMateEquation _ _ _ _ _
    (moduleDerivedAdjunction Λ f₂) (moduleDerivedAdjunction Λ f₁)
    (moduleDerivedAdjunction Λ f₀)
    (moduleDerivedOpenComparison_hComp Λ j₁ j₂ i₁ i₂ f₀ f₁ f₂ h₁ h₂ ht) K

end AlgebraicGeometry.Scheme.EtaleCohomology
