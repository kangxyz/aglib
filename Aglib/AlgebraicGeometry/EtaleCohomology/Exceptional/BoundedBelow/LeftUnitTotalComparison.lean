/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitImage
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnitTotals
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence

public import Aglib.CategoryTheory.Functor.ImageComparisonRestriction

/-! # The left-unit total map is the original mixed refinement transition -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

omit [QuasiCompact f] in
/-- The actual total structural triangle gives the original identity proper compositor. -/
theorem moduleLeftUnitTotalDirectImageIso :
    (@moduleDerivedRefinementDirectImageIso Λ _ X Y f hY
      (Hom.DenseCompactification.ofArrowEq (Category.id_comp f)
        (Hom.CompactifiedComposition.leftUnit C).composite) C
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C) hB hD) =
    (@moduleDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar)
      hY hD hB).symm := by
  change (@moduleDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar)
    hY hD hB).symm ≪≫ Iso.refl _ = _
  exact Iso.trans_refl _

/-- The dense total-refinement unit is literally the original mixed identity unit. -/
theorem moduleLeftUnitTotalRefinementDelta :
    (@moduleDerivedRefinementComparison X Y f _
      (Hom.DenseCompactification.ofArrowEq (Category.id_comp f)
        (Hom.CompactifiedComposition.leftUnit C).composite) C
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C) Λ _ hX hB hD) =
    (@moduleDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
      (𝟙 C.Xbar) (leftUnitTowerTotalSquare C) Λ _ hX hB hD) := rfl

/-- The total image face is the same original mixed transition along the actual refinement. -/
theorem moduleLeftUnitTotalMixedTransition :
    (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY
      (Hom.DenseCompactification.ofArrowEq (Category.id_comp f)
        (Hom.CompactifiedComposition.leftUnit C).composite) C
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C) hB hD) =
    CategoryTheory.imageComparison
      (L₁ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hB)
      (L₂ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD)
      (R₁ := @moduleDerivedDirectImage Y Λ _ C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY hB)
      (R₂ := @moduleDerivedDirectImage Y Λ _ C.Xbar C.p hY hD)
      (F := @moduleDerivedDirectImage C.Xbar Λ _ C.Xbar (𝟙 C.Xbar) hD hB)
      (Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
        (@moduleDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
          (𝟙 C.Xbar) (leftUnitTowerTotalSquare C) Λ _ hX hB hD))
      (@moduleDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar)
        hY hD hB).symm := by
  unfold moduleCompactificationMixedTransition
  rw [moduleLeftUnitTotalDirectImageIso, moduleLeftUnitTotalRefinementDelta]
  exact CategoryTheory.imageComparison_whiskerLeft
    (@moduleTorsionCohomologyPlus X Λ _ hX).ι _ _

end AlgebraicGeometry.Scheme.EtaleCohomology
