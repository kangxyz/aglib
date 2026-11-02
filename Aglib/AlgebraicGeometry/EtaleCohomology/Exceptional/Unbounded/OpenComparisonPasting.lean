/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.OpenComparisonPasting
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekBaseChangeMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangePasting

/-! # Pasting of the original unbounded open Cartesian comparisons -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u

section Mate
universe wV wU wY wX
variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The whole square, not merely its component, is the original inverse-image mate. -/
theorem mateEquiv_moduleUnboundedDerivedOpenComparison_inv :
    mateEquiv (moduleUnboundedDerivedLowerShriekAdjunction j Λ)
      (moduleUnboundedDerivedLowerShriekAdjunction i Λ)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).inv) =
      TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedInverseImageSquareIso Λ f g j i h.w).hom := by
  apply TwoSquare.ext
  intro K
  exact congrArg (fun t => t.app K)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_inv_mate g i j f h Λ)
end Mate

section OpenPasting

universe wU₀ wU₁ wU₂ wX₀ wX₁ wX₂

variable {U₀ U₁ U₂ X₀ X₁ X₂ : Scheme.{u}}
  (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
  (g₁ : U₁ ⟶ U₀) (g₂ : U₂ ⟶ U₁) (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁)
  [Etale j₀] [Etale j₁] [Etale j₂]
  (h₁ : IsPullback g₁ j₁ j₀ f₁) (h₂ : IsPullback g₂ j₂ j₁ f₂)
  (ht : IsPullback (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁))
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]

/-- The original open Cartesian comparisons paste through the original inverse-image
compositors. This is the inverse native-mate form of canonical square pasting. -/
theorem moduleUnboundedDerivedOpenComparison_pasting :
    LeftComparisonPastingEquation
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₁ j₁ j₀ f₁ h₁ Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₂ j₂ j₁ f₂ h₂ Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ g₁ g₂)
      (moduleUnboundedDerivedInverseImageCompIso Λ f₁ f₂) := by
  exact openComparison_pasting_of_mates
    (moduleUnboundedDerivedLowerShriekAdjunction j₀ Λ)
    (moduleUnboundedDerivedLowerShriekAdjunction j₁ Λ)
    (moduleUnboundedDerivedLowerShriekAdjunction j₂ Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₁ j₁ j₀ f₁ h₁ Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₂ j₂ j₁ f₂ h₂ Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ g₁ g₂)
    (moduleUnboundedDerivedInverseImageCompIso Λ f₁ f₂)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₁ g₁ j₀ j₁ h₁.w).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₂ g₂ j₁ j₂ h₂.w).hom)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ (f₂ ≫ f₁) (g₂ ≫ g₁) j₀ j₂ ht.w).hom)
    (mateEquiv_moduleUnboundedDerivedOpenComparison_inv g₁ j₁ j₀ f₁ h₁ Λ)
    (mateEquiv_moduleUnboundedDerivedOpenComparison_inv g₂ j₂ j₁ f₂ h₂ Λ)
    (mateEquiv_moduleUnboundedDerivedOpenComparison_inv (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ)
    (moduleUnboundedDerivedInverseImageSquareIso_vComp Λ f₁ f₂ g₁ g₂ j₀ j₁ j₂ h₁.w h₂.w ht.w)

end OpenPasting

end AlgebraicGeometry.Scheme.EtaleCohomology
