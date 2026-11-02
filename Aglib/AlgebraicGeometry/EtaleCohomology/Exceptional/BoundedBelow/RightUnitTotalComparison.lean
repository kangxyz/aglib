/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitProperFace
public import
  Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionRightUnitRefinements
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence
public import Aglib.CategoryTheory.Functor.ImageComparisonRestrictionCongruence

/-! # The right-unit raw image comparison is the original first-to-total transition -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ))
  (hA : HasDerivedCategory.{wA} (ModuleSheaf (rightUnitFirstAmbient C) Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))

omit [QuasiCompact f] in
/-- The actual first-to-total structural map retains the literal composite `p ≫ id`. -/
theorem moduleRightUnitTotalDirectImageIso :
    (@moduleDerivedRefinementDirectImageIso Λ _ X Y f hY
      (Hom.CompactifiedComposition.rightUnit C).first
      (Hom.DenseCompactification.ofArrowEq (Category.comp_id f)
        (Hom.CompactifiedComposition.rightUnit C).composite)
      (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C) hA hB) =
    moduleRightUnitMiddleOverIso C Λ hY hA hB := rfl

/-- The actual first-to-total source map is precisely the original mixed refinement unit. -/
theorem moduleRightUnitTotalRefinementDelta :
    (@moduleDerivedRefinementComparison X Y f _
      (Hom.CompactifiedComposition.rightUnit C).first
      (Hom.DenseCompactification.ofArrowEq (Category.comp_id f)
        (Hom.CompactifiedComposition.rightUnit C).composite)
      (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C) Λ _ hX hA hB) =
    (@moduleDerivedProperRefinementComparison X (rightUnitFirstAmbient C) C.Xbar
      (rightUnitFirstOpen C) C.j _ _ (rightUnitMiddleOpen C)
      (rightUnitOpenTotalSquare C) Λ _ hX hA hB) := rfl

/-- No new comparison is chosen: the raw right-unit face is the original mixed transition. -/
theorem moduleRightUnitTotalMixedTransition :
    (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY
      (Hom.CompactifiedComposition.rightUnit C).first
      (Hom.DenseCompactification.ofArrowEq (Category.comp_id f)
        (Hom.CompactifiedComposition.rightUnit C).composite)
      (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C) hA hB) =
    CategoryTheory.imageComparison
      (L₁ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
        @moduleDerivedLowerShriek X (rightUnitFirstAmbient C)
          (rightUnitFirstOpen C) _ Λ _ hX hA)
      (L₂ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hB)
      (R₁ := @moduleDerivedDirectImage Y Λ _ (rightUnitFirstAmbient C)
        (Hom.CompactifiedComposition.rightUnit C).first.p hY hA)
      (R₂ := @moduleDerivedDirectImage Y Λ _ C.Xbar (C.p ≫ 𝟙 Y) hY hB)
      (F := @moduleDerivedDirectImage C.Xbar Λ _ (rightUnitFirstAmbient C)
        (rightUnitMiddleOpen C) hB hA)
      (Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
        (@moduleDerivedProperRefinementComparison X (rightUnitFirstAmbient C) C.Xbar
          (rightUnitFirstOpen C) C.j _ _ (rightUnitMiddleOpen C)
          (rightUnitOpenTotalSquare C) Λ _ hX hA hB))
      (moduleRightUnitMiddleOverIso C Λ hY hA hB) :=
  CategoryTheory.imageComparison_whiskerLeft_of_eq
    (L₁ := @moduleDerivedLowerShriek X (rightUnitFirstAmbient C)
      (rightUnitFirstOpen C) _ Λ _ hX hA)
    (L₂ := @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hB)
    (R₁ := @moduleDerivedDirectImage Y Λ _ (rightUnitFirstAmbient C)
      (Hom.CompactifiedComposition.rightUnit C).first.p hY hA)
    (R₂ := @moduleDerivedDirectImage Y Λ _ C.Xbar (C.p ≫ 𝟙 Y) hY hB)
    (F := @moduleDerivedDirectImage C.Xbar Λ _ (rightUnitFirstAmbient C)
      (rightUnitMiddleOpen C) hB hA)
    (@moduleTorsionCohomologyPlus X Λ _ hX).ι
    (@moduleDerivedRefinementComparison X Y f _
      (Hom.CompactifiedComposition.rightUnit C).first
      (Hom.DenseCompactification.ofArrowEq (Category.comp_id f)
        (Hom.CompactifiedComposition.rightUnit C).composite)
      (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C) Λ _ hX hA hB)
    (@moduleDerivedProperRefinementComparison X (rightUnitFirstAmbient C) C.Xbar
      (rightUnitFirstOpen C) C.j _ _ (rightUnitMiddleOpen C)
      (rightUnitOpenTotalSquare C) Λ _ hX hA hB)
    (@moduleDerivedRefinementDirectImageIso Λ _ X Y f hY
      (Hom.CompactifiedComposition.rightUnit C).first
      (Hom.DenseCompactification.ofArrowEq (Category.comp_id f)
        (Hom.CompactifiedComposition.rightUnit C).composite)
      (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C) hA hB)
    (moduleRightUnitMiddleOverIso C Λ hY hA hB)
    (moduleRightUnitTotalRefinementDelta C Λ hX hA hB)
    (moduleRightUnitTotalDirectImageIso C Λ hY hA hB)

end AlgebraicGeometry.Scheme.EtaleCohomology
