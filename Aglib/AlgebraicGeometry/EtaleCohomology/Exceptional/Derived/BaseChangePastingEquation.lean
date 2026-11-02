/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangePasting

/-! # Whole-equation boundary for original consecutive proper base change -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wb0 wb1 wb2 wb3 wb4 wb5
variable (Λ : Type (u + 1)) [Ring Λ]

section Horizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  [HasDerivedCategory.{wb0} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wb1} (ModuleSheaf S₀ Λ)]
  [HasDerivedCategory.{wb2} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wb3} (ModuleSheaf S₁ Λ)]
  [HasDerivedCategory.{wb4} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wb5} (ModuleSheaf S₂ Λ)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- The original consecutive proper exchange law, retained as one predicate. -/
theorem moduleDerivedBaseChangeMap_hComp_equation
    (K : DerivedCategory.Plus (ModuleSheaf X₀ Λ)) :
    ActualHorizontalMateEquation
      (moduleDerivedBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁)
      (moduleDerivedBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂)
      (moduleDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
      (moduleDerivedInverseImageCompIso Λ g₁ g₂).hom
      (moduleDerivedInverseImageCompIso Λ h₁ h₂).hom K := by
  exact actualHorizontalMateEquation_of_mates
    (moduleDerivedAdjunction Λ f₀) (moduleDerivedAdjunction Λ f₁)
    (moduleDerivedAdjunction Λ f₂)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
    (moduleDerivedInverseImageCompIso Λ g₁ g₂).hom
    (moduleDerivedInverseImageCompIso Λ h₁ h₂).hom
    (moduleDerivedBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁) (moduleDerivedBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂)
    (moduleDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    rfl
    rfl
    rfl K
    (horizontalMateEquation _ _ _ _ _
      (moduleDerivedAdjunction Λ f₀) (moduleDerivedAdjunction Λ f₁)
    (moduleDerivedAdjunction Λ f₂)
      (moduleDerivedInverseImageSquareIso_hComp Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) K)

end Horizontal

end AlgebraicGeometry.Scheme.EtaleCohomology
