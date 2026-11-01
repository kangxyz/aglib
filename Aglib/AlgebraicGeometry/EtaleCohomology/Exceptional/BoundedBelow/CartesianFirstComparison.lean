/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianFirstNaturality
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionCanonical

/-! # A changed Cartesian first presentation retains the actual original supplied compositor -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wC wG wFG
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wC} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  [hF : HasDerivedCategory.{wF} (ModuleSheaf F.Xbar Λ)]
  (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (hj : F.j ≫ m = C.sourceCompactification.j)

include sqMid in
/-- The original first-refinement map followed by the raw map is the actual original alpha. -/
theorem moduleCartesianFirstComparison :
    Functor.whiskerRight
        (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY
          F C.first a hF (firstModels C.first))
        (@moduleDerivedLowerShriek Y C.targetCompactification.Xbar
            C.targetCompactification.j _ Λ _ hY (targetModels C.targetCompactification) ⋙
          @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
            C.targetCompactification.p hZ (targetModels C.targetCompactification)) ≫
      moduleCartesianCompositionMap C F m sq hj Λ hX hY hZ hF
        (targetModels C.targetCompactification) (compositeModels C.composite) =
    (moduleCompactifiedCompositionAmbientIso f g Λ C).hom := by
  have he := moduleCartesianFirstRefinementEquation
    (hX := hX) (hY := hY) (hZ := hZ) (hF := hF)
    (hC := firstModels C.first) (hG := targetModels C.targetCompactification)
    (hFG := compositeModels C.composite) C F m sq a sqMid hj Λ
  exact he.trans (moduleCartesianCompositionMap_canonical f g Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
