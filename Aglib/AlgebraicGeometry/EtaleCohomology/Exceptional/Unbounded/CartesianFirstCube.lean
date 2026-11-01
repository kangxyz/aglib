/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianFirstStructural
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianFirstHorizontal
public import Aglib.CategoryTheory.Functor.ImageCompositionRefinement

/-! # The original cube comparing a Cartesian first presentation with the canonical pullback -/

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
local instance unboundedCartesianFirstCubeCategory :
    Category.{wFG} (@DerivedCategory (ModuleSheaf C.composite.Xbar Λ)
      inferInstance inferInstance hFG) :=
  @instCategoryDerivedCategory (ModuleSheaf C.composite.Xbar Λ)
    inferInstance inferInstance hFG

include sqMid in
/-- Three proved original faces imply the exact first-presentation cube. -/
theorem moduleUnboundedCartesianFirstRefinementCube :
    ImageCompositionRefinementEquation
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
        C.composite C.composite (𝟙 C.composite) hFG hFG) := by
  let σ := moduleUnboundedProperOpenMate a.hom m C.middleOpen (𝟙 C.sourceCompactification.Xbar)
    sqMid.flip Λ
  let r := moduleUnboundedProperOpenRefinementTargetIso Λ C.sourceCompactification.p
    C.sourceCompactification.p (𝟙 C.sourceCompactification.Xbar)
    (𝟙 C.targetCompactification.Xbar) (unboundedCartesianFirstProperSquare C)
  exact imageCompositionRefinementEquation _ _ _ _ _ σ _ _ _ _ r _ _ _
    (moduleUnboundedCartesianCompositionRefinementHorizontal C F m a sqMid hj Λ
      (hX := hX) (hF := hF) (hC := hC) (hFG := hFG))
    (moduleUnboundedCartesianFirstRefinementRectangle C F m sq a sqMid Λ)
    (moduleUnboundedCartesianFirstStructuralEquation C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
