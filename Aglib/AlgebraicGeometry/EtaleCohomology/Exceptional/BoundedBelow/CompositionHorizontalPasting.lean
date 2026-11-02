/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.HorizontalCoherence
public import Aglib.CategoryTheory.Functor.ImageInterchangeHorizontal

/-! # Whole original horizontal input for exceptional composition associativity -/

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

/-- Original horizontal proper/open pasting in the exact predicate of the abstract core. -/
theorem moduleProperOpenMate_hComp_interchange :
    ImageHorizontalInterchange
      (moduleProperOpenMate Λ j₂ i₂ f₂ f₁ h₂)
      (moduleProperOpenMate Λ j₁ i₁ f₁ f₀ h₁)
      (moduleProperOpenMate Λ (j₂ ≫ j₁) (i₂ ≫ i₁) f₂ f₀ ht)
      (moduleDerivedLowerShriekCompIso Λ j₁ j₂)
      (moduleDerivedLowerShriekCompIso Λ i₁ i₂) :=
  imageHorizontalInterchange_of_mates
    (moduleDerivedAdjunction Λ f₂) (moduleDerivedAdjunction Λ f₁)
    (moduleDerivedAdjunction Λ f₀)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ).hom)
    (moduleDerivedLowerShriekCompIso Λ j₁ j₂)
    (moduleDerivedLowerShriekCompIso Λ i₁ i₂)
    _ _ _ rfl rfl rfl
    (moduleProperOpenMate_hComp Λ j₁ j₂ i₁ i₂ f₀ f₁ f₂ h₁ h₂ ht)

end AlgebraicGeometry.Scheme.EtaleCohomology
