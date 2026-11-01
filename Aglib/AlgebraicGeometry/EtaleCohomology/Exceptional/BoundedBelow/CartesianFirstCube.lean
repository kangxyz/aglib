/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianFirstStructural
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianFirstHorizontal
public import Aglib.CategoryTheory.Functor.ImageCompositionRefinement

/-! # The original cube comparing a Cartesian first presentation with the canonical pullback -/

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
/-- Three proved original faces imply the exact first-presentation cube. -/
theorem moduleCartesianFirstRefinementCube :
    ImageCompositionRefinementEquation
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
        C.composite C.composite (𝟙 C.composite) hFG hFG) := by
  let σ := moduleProperOpenMate Λ C.middleOpen m a.hom
    (𝟙 C.sourceCompactification.Xbar) sqMid.flip
  let r := moduleProperOpenRefinementTargetIso Λ C.sourceCompactification.p
    C.sourceCompactification.p (𝟙 C.sourceCompactification.Xbar)
    (𝟙 C.targetCompactification.Xbar) (cartesianFirstProperSquare C)
  exact imageCompositionRefinementEquation _ _ _ _ _ σ _ _ _ _ r _ _ _
    (moduleCartesianCompositionRefinementHorizontal C F m a sqMid hj Λ hX hF hC hFG)
    (moduleCartesianFirstRefinementRectangle C F m sq a sqMid Λ)
    (moduleCartesianFirstStructuralEquation C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
