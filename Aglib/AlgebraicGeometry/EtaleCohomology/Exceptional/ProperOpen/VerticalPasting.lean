/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Coherence
public import Aglib.CategoryTheory.Adjunction.NaturalPastedRectangle

/-! # Whole original vertical proper/open route equations -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU₀ wU₁ wU₂ wX₀ wX₁ wX₂

variable (Λ : Type (u + 1)) [Ring Λ]

variable {U₀ U₁ U₂ X₀ X₁ X₂ : Scheme.{u}}
  (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
  (g₁ : U₁ ⟶ U₀) (g₂ : U₂ ⟶ U₁) (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁)
  [Etale j₀] [Etale j₁] [Etale j₂]
  (h₁ : IsPullback g₁ j₁ j₀ f₁) (h₂ : IsPullback g₂ j₂ j₁ f₂)
  (ht : IsPullback (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁))
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]

/-- The proved original vertical pasting, retained as one actual-map family. -/
theorem moduleProperOpenMate_vComp_actual :
    ActualVerticalMatePasting
      (moduleProperOpenMate Λ j₀ j₁ g₁ f₁ h₁)
      (moduleProperOpenMate Λ j₁ j₂ g₂ f₂ h₂)
      (moduleProperOpenMate Λ j₀ j₂ (g₂ ≫ g₁) (f₂ ≫ f₁) ht)
      (moduleDerivedDirectImageCompIso Λ g₁ g₂).hom
      (moduleDerivedDirectImageCompIso Λ f₁ f₂).hom :=
  actualVerticalMatePasting_of_mates
    (moduleDerivedAdjunction Λ g₁) (moduleDerivedAdjunction Λ f₁)
    (moduleDerivedAdjunction Λ g₂) (moduleDerivedAdjunction Λ f₂)
    (moduleDerivedAdjunction Λ (g₂ ≫ g₁))
    (moduleDerivedAdjunction Λ (f₂ ≫ f₁))
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso g₁ j₁ j₀ f₁ h₁ Λ).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso g₂ j₂ j₁ f₂ h₂ Λ).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso
        (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ).hom)
    (moduleDerivedDirectImageCompIso Λ g₁ g₂)
    (moduleDerivedDirectImageCompIso Λ f₁ f₂)
    (moduleProperOpenMate Λ j₀ j₁ g₁ f₁ h₁)
    (moduleProperOpenMate Λ j₁ j₂ g₂ f₂ h₂)
    (moduleProperOpenMate Λ j₀ j₂ (g₂ ≫ g₁) (f₂ ≫ f₁) ht)
    rfl rfl rfl
    (moduleProperOpenMate_vComp_mate Λ j₀ j₁ j₂ g₁ g₂ f₁ f₂ h₁ h₂ ht)

end AlgebraicGeometry.Scheme.EtaleCohomology
