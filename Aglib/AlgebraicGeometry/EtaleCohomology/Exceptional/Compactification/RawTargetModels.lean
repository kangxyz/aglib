/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.TargetModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification

/-! # Canonical target transport of raw compactifications and original densification -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS₀ wS₁ wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))

/-- Canonical native target transport of the original raw open/proper value. -/
def moduleRawCompactificationTargetComparison :
    @moduleRawCompactificationFunctor X S f C Λ _ hX hS₀ hC ⋙
        (canonicalEquivalence hS₀ hS₁).functor ≅
      @moduleRawCompactificationFunctor X S f C Λ _ hX hS₁ hC :=
  imageTargetIso ((@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
    @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hC)
    (moduleDerivedDirectImageTargetIso Λ hC hS₀ hS₁ C.p)

variable [QuasiCompact C.j]
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.densify.Xbar Λ))

/-- The original closed-densification comparison commutes with native target transport. -/
theorem moduleCompactificationDensification_targetModel :
    Functor.isoWhiskerRight
        (@moduleCompactificationDensificationIso X S f C _ Λ _ hX hS₀ hC hD)
          (canonicalEquivalence hS₀ hS₁).functor ≪≫
        moduleRawCompactificationTargetComparison C.densify.toCompactification Λ hX hS₀ hS₁ hD =
      moduleRawCompactificationTargetComparison C Λ hX hS₀ hS₁ hC ≪≫
        @moduleCompactificationDensificationIso X S f C _ Λ _ hX hS₁ hC hD := by
  apply Iso.ext
  exact imageComparison_target
    (L₁ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
      @moduleDerivedLowerShriek X C.densify.Xbar C.densify.j _ Λ _ hX hD)
    (L₂ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
      @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hC)
    (F := (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC (moduleDirectImage
      (Hom.Compactification.densifyι C) Λ) _ _))
    (Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
      (@moduleDerivedProperRefinementComparison X C.densify.Xbar C.Xbar C.densify.j C.j _ _
        (Hom.Compactification.densifyι C) (Hom.Compactification.isPullback_densify C)
        Λ _ hX hD hC))
    (@moduleDerivedDirectImageOverIso Λ _ S C.densify.Xbar C.Xbar hS₀ hD hC
      C.densify.p C.p (Hom.Compactification.densifyι C) (Hom.Compactification.densifyι_p C))
    (@moduleDerivedDirectImageOverIso Λ _ S C.densify.Xbar C.Xbar hS₁ hD hC
      C.densify.p C.p (Hom.Compactification.densifyι C) (Hom.Compactification.densifyι_p C))
    (moduleDerivedDirectImageTargetIso Λ hD hS₀ hS₁ C.densify.p)
    (moduleDerivedDirectImageTargetIso Λ hC hS₀ hS₁ C.p)
    (moduleDerivedDirectImageTargetIso_over Λ hD hC hS₀ hS₁
      C.densify.p C.p (Hom.Compactification.densifyι C) (Hom.Compactification.densifyι_p C))

end AlgebraicGeometry.Scheme.EtaleCohomology
