/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageFirstTargetRefinement
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionSingleTarget
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianFirstNaturality

/-! # Actual first refinement and independent total-model transport in one original square -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wC wG wT₀ wT₁
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  [hF : HasDerivedCategory.{wF} (ModuleSheaf F.Xbar Λ)]
  [hC : HasDerivedCategory.{wC} (ModuleSheaf C.first.Xbar Λ)]
  [hG : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ)]
  (hT₀ : HasDerivedCategory.{wT₀} (ModuleSheaf C.sourceCompactification.Xbar Λ))
  (hT₁ : HasDerivedCategory.{wT₁} (ModuleSheaf C.sourceCompactification.Xbar Λ))
  (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (hj : F.j ≫ m = C.sourceCompactification.j)

include sqMid in
/-- No source or target family is patched to identify the two original maps. -/
theorem moduleUnboundedCartesianFirstTargetComparison :
    ImageFirstTargetEquation
      (K₀ := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hC)
      (K₁ := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
      (Q₀ := @moduleUnboundedDerivedDirectImage Λ _ Y C.first.Xbar C.first.p hY hC)
      (Q₁ := @moduleUnboundedDerivedDirectImage Λ _ Y F.Xbar F.p hY hF)
      (I := @moduleUnboundedDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P := @moduleUnboundedDerivedDirectImage Λ _ Z C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (J₀ := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hT₀)
      (J₁ := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hT₁)
      (S₀ := @moduleUnboundedDerivedDirectImage Λ _ Z C.sourceCompactification.Xbar C.composite.p
        hZ hT₀)
      (S₁ := @moduleUnboundedDerivedDirectImage Λ _ Z C.sourceCompactification.Xbar C.composite.p
        hZ hT₁)
      (@moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY F C.first a hF hC)
      (@moduleUnboundedCompactificationMixedTransition X Z (f ≫ g) _ Λ _ hX hZ
        C.composite C.composite (𝟙 C.composite) hT₁ hT₀)
      (moduleUnboundedCartesianCompositionUnderlyingMap C C.first C.middleOpen
        C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hC hG hT₀)
      (moduleUnboundedCartesianCompositionUnderlyingMap C F m sq hj Λ hX hY hZ hF hG hT₁) := by
  exact imageFirstTargetEquation _ _ _ _ _
    (moduleUnboundedCartesianFirstRefinementEquation
      (hX := hX) (hY := hY) (hZ := hZ) (hF := hF) (hC := hC) (hG := hG) (hFG := hT₁)
      C F m sq a sqMid hj Λ)
    (moduleUnboundedCartesianCompositionUnderlyingMap_singleTarget f g Λ C hT₀ hT₁)

end AlgebraicGeometry.Scheme.EtaleCohomology
