/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianFirstCube
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionIdentity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence
public import Aglib.CategoryTheory.Functor.CartesianImageNaturality
public import Aglib.CategoryTheory.Functor.ImageFirstRefinement

/-! # The original naturality equation for a changed Cartesian first presentation -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wC wG wFG
variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g]
  (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (hj : F.j ≫ m = C.sourceCompactification.j)
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hF : HasDerivedCategory.{wF} (ModuleSheaf F.Xbar Λ)]
  [hC : HasDerivedCategory.{wC} (ModuleSheaf C.first.Xbar Λ)]
  [hG : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ)]
  [hFG : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ)]

include sqMid in
/-- All original comparison formulas retain the proved first-presentation cube. -/
theorem moduleCartesianFirstNaturality :
    ImageCompositionNaturalityEquation
      (K₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hC)
      (K₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
      (J₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (J₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (Q₀ := @moduleDerivedDirectImage Y Λ _ C.first.Xbar C.first.p hY hC)
      (Q₁ := @moduleDerivedDirectImage Y Λ _ F.Xbar F.p hY hF)
      (I₀ := @moduleDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (I₁ := @moduleDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P₀ := @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (P₁ := @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (S₀ := @moduleDerivedDirectImage Z Λ _ C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
      (S₁ := @moduleDerivedDirectImage Z Λ _ C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
      (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY F C.first a hF hC)
      (CategoryTheory.imageComparison
        (moduleDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
        (moduleDerivedRefinementDirectImageIso Λ (𝟙 C.targetCompactification)))
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (CategoryTheory.imageComparison
          (@moduleDerivedRefinementComparison X Z (f ≫ g) _ C.composite C.composite
            (𝟙 C.composite) Λ _ hX hFG hFG)
          (@moduleDerivedRefinementDirectImageIso Λ _ X Z (f ≫ g) hZ
            C.composite C.composite (𝟙 C.composite) hFG hFG)))
      (moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hC hG hFG)
      (moduleCartesianCompositionMap C F m sq hj Λ hX hY hZ hF hG hFG) :=
  cartesianImageNaturality (moduleTorsionCohomologyPlus X Λ).ι
    (moduleDerivedRefinementComparison a Λ)
    (moduleDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
    (@moduleDerivedRefinementComparison X Z (f ≫ g) _ C.composite C.composite
      (𝟙 C.composite) Λ _ hX hFG hFG)
    (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
      C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
    (moduleProperOpenMate Λ C.targetCompactification.j m F.p C.sourceCompactification.p sq.flip)
    (moduleCartesianCompositionOpenIso C C.first C.middleOpen C.first_j_middleOpen
      Λ hX hC hFG)
    (moduleCartesianCompositionOpenIso C F m hj Λ hX hF hFG)
    (moduleDerivedRefinementDirectImageIso Λ a)
    (moduleDerivedRefinementDirectImageIso Λ (𝟙 C.targetCompactification))
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (@moduleDerivedRefinementDirectImageIso Λ _ X Z (f ≫ g) hZ
      C.composite C.composite (𝟙 C.composite) hFG hFG)
    (moduleCartesianFirstRefinementCube C F m sq a sqMid hj Λ)

include sqMid in
/-- The two unchanged original identity faces leave only the actual first-refinement map. -/
theorem moduleCartesianFirstRefinementEquation :
    ImageFirstRefinementEquation
      (K₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hC)
      (K₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (Q₀ := @moduleDerivedDirectImage Y Λ _ C.first.Xbar C.first.p hY hC)
      (Q₁ := @moduleDerivedDirectImage Y Λ _ F.Xbar F.p hY hF)
      (I := @moduleDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P := @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (S := @moduleDerivedDirectImage Z Λ _ C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
      (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY F C.first a hF hC)
      (moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hC hG hFG)
      (moduleCartesianCompositionMap C F m sq hj Λ hX hY hZ hF hG hFG) :=
  imageFirstRefinementEquation
      (K₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hC)
      (K₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (Q₀ := @moduleDerivedDirectImage Y Λ _ C.first.Xbar C.first.p hY hC)
      (Q₁ := @moduleDerivedDirectImage Y Λ _ F.Xbar F.p hY hF)
      (I := @moduleDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P := @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (S := @moduleDerivedDirectImage Z Λ _ C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
    (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY F C.first a hF hC)
    (CategoryTheory.imageComparison
        (moduleDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
        (moduleDerivedRefinementDirectImageIso Λ (𝟙 C.targetCompactification)))
    (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (CategoryTheory.imageComparison
          (@moduleDerivedRefinementComparison X Z (f ≫ g) _ C.composite C.composite
            (𝟙 C.composite) Λ _ hX hFG hFG)
          (@moduleDerivedRefinementDirectImageIso Λ _ X Z (f ≫ g) hZ
            C.composite C.composite (𝟙 C.composite) hFG hFG)))
    (moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hC hG hFG)
    (moduleCartesianCompositionMap C F m sq hj Λ hX hY hZ hF hG hFG)
    (@moduleDerivedCompactificationImageIdentity Y Z g _ Λ _ hY hZ
      C.targetCompactification hG)
    (@moduleDerivedCompactificationImageIdentity_torsion X Z (f ≫ g) _ Λ _ hX hZ
      C.composite hFG)
    (moduleCartesianFirstNaturality C F m sq a sqMid hj Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
