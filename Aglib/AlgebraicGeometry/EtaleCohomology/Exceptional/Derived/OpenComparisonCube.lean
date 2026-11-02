/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.TwoSidedMateIsomorphism
public import Aglib.CategoryTheory.Adjunction.OpenComparisonPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CartesianExchangeComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangePasting
public import Aglib.CategoryTheory.Adjunction.Mates
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperComparison

/-! # Original open comparisons and Cartesian cube coherence

The open comparison is identified through the native mate equivalence, before
any scheme-level pasting or identity normalization. No replacement map is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wV wU wY wX

variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Taking the original open-adjunction mate of the inverse lower-shriek
comparison recovers precisely the canonical inverse-image square. -/
theorem mateEquiv_moduleDerivedOpenComparison_inv :
    mateEquiv (moduleDerivedLowerShriekAdjunction j Λ)
      (moduleDerivedLowerShriekAdjunction i Λ)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).inv) =
      TwoSquare.mk _ _ _ _
        (moduleDerivedInverseImageSquareIso Λ f g j i h.w).hom := by
  have hm := mateEquiv_inv_eq_of_conjugate
    (moduleDerivedLowerShriekAdjunction j Λ) (moduleDerivedLowerShriekAdjunction i Λ)
    (moduleDerivedAdjunction Λ g) (moduleDerivedAdjunction Λ f)
    (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ)
    (moduleDerivedCartesianExchangeIso g i j f h Λ)
    (moduleDerivedInverseImageSquareIso Λ f g j i h.w).hom
    (conjugateEquiv_moduleDerivedLowerShriekCartesianBaseChangeIso_hom g i j f h Λ)
    (moduleDerivedCartesianExchangeIso_hom g i j f h Λ).symm
  apply TwoSquare.ext
  intro K
  exact NatTrans.congr_app hm K

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients
open TwoSquare

universe u

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
theorem moduleDerivedOpenComparison_pasting :
    LeftComparisonPastingEquation
      (moduleDerivedLowerShriekCartesianBaseChangeIso g₁ j₁ j₀ f₁ h₁ Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso g₂ j₂ j₁ f₂ h₂ Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ)
      (moduleDerivedInverseImageCompIso Λ g₁ g₂)
      (moduleDerivedInverseImageCompIso Λ f₁ f₂) := by
  exact openComparison_pasting_of_mates
    (moduleDerivedLowerShriekAdjunction j₀ Λ) (moduleDerivedLowerShriekAdjunction j₁ Λ)
    (moduleDerivedLowerShriekAdjunction j₂ Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso g₁ j₁ j₀ f₁ h₁ Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso g₂ j₂ j₁ f₂ h₂ Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ)
    (moduleDerivedInverseImageCompIso Λ g₁ g₂) (moduleDerivedInverseImageCompIso Λ f₁ f₂)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₁ g₁ j₀ j₁ h₁.w).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₂ g₂ j₁ j₂ h₂.w).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedInverseImageSquareIso Λ (f₂ ≫ f₁) (g₂ ≫ g₁) j₀ j₂ ht.w).hom)
    (mateEquiv_moduleDerivedOpenComparison_inv g₁ j₁ j₀ f₁ h₁ Λ)
    (mateEquiv_moduleDerivedOpenComparison_inv g₂ j₂ j₁ f₂ h₂ Λ)
    (mateEquiv_moduleDerivedOpenComparison_inv (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ)
    (moduleDerivedInverseImageSquareIso_vComp Λ f₁ f₂ g₁ g₂ j₀ j₁ j₂ h₁.w h₂.w ht.w)

end OpenPasting

end AlgebraicGeometry.Scheme.EtaleCohomology
