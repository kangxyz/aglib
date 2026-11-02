/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianFirstCube
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianCompositionIdentity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedModelTransition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonFormulas
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianUnderlyingMap
public import Aglib.CategoryTheory.Functor.ImageFirstRefinement

/-! # The original naturality equation for a changed Cartesian first presentation -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard
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

/-- The category structure for the specified derived-category model. -/
local instance unboundedCartesianFirstNaturalityCategory :
    Category.{wFG} (@DerivedCategory (ModuleSheaf C.composite.Xbar Λ)
      inferInstance inferInstance hFG) :=
  @instCategoryDerivedCategory (ModuleSheaf C.composite.Xbar Λ)
    inferInstance inferInstance hFG

include sqMid in
/-- All original comparison formulas retain the proved first-presentation cube. -/
theorem moduleUnboundedCartesianFirstNaturality :
    ImageCompositionNaturalityEquation
      (K₀ := @moduleUnboundedDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hC)
      (K₁ := @moduleUnboundedDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
      (J₀ := @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (J₁ := @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (Q₀ := @moduleUnboundedDerivedDirectImage Λ _ Y C.first.Xbar C.first.p hY hC)
      (Q₁ := @moduleUnboundedDerivedDirectImage Λ _ Y F.Xbar F.p hY hF)
      (I₀ := @moduleUnboundedDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (I₁ := @moduleUnboundedDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P₀ := @moduleUnboundedDerivedDirectImage Λ _ Z C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (P₁ := @moduleUnboundedDerivedDirectImage Λ _ Z C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (S₀ := @moduleUnboundedDerivedDirectImage Λ _ Z C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
      (S₁ := @moduleUnboundedDerivedDirectImage Λ _ Z C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
      (@moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY F C.first a hF hC)
      (CategoryTheory.imageComparison
        (moduleUnboundedDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
        (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C.targetCompactification)))
      (CategoryTheory.imageComparison
          (@moduleUnboundedDerivedRefinementComparison X Z (f ≫ g) _ C.composite C.composite
            (𝟙 C.composite) Λ _ hX hFG hFG)
          (@moduleUnboundedDerivedRefinementDirectImageIso Λ _ X Z (f ≫ g) hZ
            C.composite C.composite (𝟙 C.composite) hFG hFG))
      (moduleUnboundedCartesianCompositionUnderlyingMap C C.first C.middleOpen
        C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hC hG hFG)
      (moduleUnboundedCartesianCompositionUnderlyingMap C F m sq hj Λ hX hY hZ hF hG hFG) :=
  imageCompositionNaturalityEquation
    (moduleUnboundedDerivedRefinementComparison a Λ)
    (moduleUnboundedDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
    (@moduleUnboundedDerivedRefinementComparison X Z (f ≫ g) _ C.composite C.composite
      (𝟙 C.composite) Λ _ hX hFG hFG)
    (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
    (moduleUnboundedProperOpenMate F.p m C.targetCompactification.j C.sourceCompactification.p
      sq.flip Λ)
    (moduleUnboundedCartesianCompositionOpenIso C C.first C.middleOpen C.first_j_middleOpen
      Λ hX hC hFG)
    (moduleUnboundedCartesianCompositionOpenIso C F m hj Λ hX hF hFG)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C.targetCompactification))
    (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (@moduleUnboundedDerivedRefinementDirectImageIso Λ _ X Z (f ≫ g) hZ
      C.composite C.composite (𝟙 C.composite) hFG hFG)
    _ _ _ _ _
    (moduleUnboundedCartesianFirstRefinementCube C F m sq a sqMid hj Λ)
    (imageComparisonFormula _ _) (imageComparisonFormula _ _) (imageComparisonFormula _ _)
    (imageCompositionMap_formula _ _ _) (imageCompositionMap_formula _ _ _)

include sqMid in
/-- The two unchanged original identity faces leave only the actual first-refinement map. -/
theorem moduleUnboundedCartesianFirstRefinementEquation :
    ImageFirstRefinementEquation
      (K₀ := @moduleUnboundedDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hC)
      (K₁ := @moduleUnboundedDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
      (J := @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (Q₀ := @moduleUnboundedDerivedDirectImage Λ _ Y C.first.Xbar C.first.p hY hC)
      (Q₁ := @moduleUnboundedDerivedDirectImage Λ _ Y F.Xbar F.p hY hF)
      (I := @moduleUnboundedDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P := @moduleUnboundedDerivedDirectImage Λ _ Z C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (S := @moduleUnboundedDerivedDirectImage Λ _ Z C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
      (@moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY F C.first a hF hC)
      (moduleUnboundedCartesianCompositionUnderlyingMap C C.first C.middleOpen
        C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hC hG hFG)
      (moduleUnboundedCartesianCompositionUnderlyingMap C F m sq hj Λ hX hY hZ hF hG hFG) :=
  imageFirstRefinementEquation
      (K₀ := @moduleUnboundedDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hC)
      (K₁ := @moduleUnboundedDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
      (J := @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hFG)
      (Q₀ := @moduleUnboundedDerivedDirectImage Λ _ Y C.first.Xbar C.first.p hY hC)
      (Q₁ := @moduleUnboundedDerivedDirectImage Λ _ Y F.Xbar F.p hY hF)
      (I := @moduleUnboundedDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P := @moduleUnboundedDerivedDirectImage Λ _ Z C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (S := @moduleUnboundedDerivedDirectImage Λ _ Z C.sourceCompactification.Xbar
        (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
    (@moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY F C.first a hF hC)
    (CategoryTheory.imageComparison
        (moduleUnboundedDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
        (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C.targetCompactification)))
    (CategoryTheory.imageComparison
          (@moduleUnboundedDerivedRefinementComparison X Z (f ≫ g) _ C.composite C.composite
            (𝟙 C.composite) Λ _ hX hFG hFG)
          (@moduleUnboundedDerivedRefinementDirectImageIso Λ _ X Z (f ≫ g) hZ
            C.composite C.composite (𝟙 C.composite) hFG hFG))
    (moduleUnboundedCartesianCompositionUnderlyingMap C C.first C.middleOpen
      C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hC hG hFG)
    (moduleUnboundedCartesianCompositionUnderlyingMap C F m sq hj Λ hX hY hZ hF hG hFG)
    (@moduleUnboundedDerivedCompactificationImageIdentity Y Z g _ Λ _ hY hZ
      C.targetCompactification hG)
    (@moduleUnboundedDerivedCompactificationImageIdentity X Z (f ≫ g) _ Λ _ hX hZ
      C.composite hFG)
    (moduleUnboundedCartesianFirstNaturality C F m sq a sqMid hj Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
