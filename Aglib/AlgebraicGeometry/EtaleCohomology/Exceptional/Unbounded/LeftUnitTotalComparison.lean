/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitImage
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnitTotals
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedModelTransition


/-! # The left-unit total map is the original mixed refinement transition -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ)]
  [hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ)]

omit [QuasiCompact f] hX in
/-- The actual total structural triangle gives the original identity proper compositor. -/
theorem moduleUnboundedLeftUnitTotalDirectImageIso :
    (@moduleUnboundedDerivedRefinementDirectImageIso Λ _ X Y f hY
      (Hom.DenseCompactification.ofArrowEq (Category.id_comp f)
        (Hom.CompactifiedComposition.leftUnit C).composite) C
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C) hB hD) =
    (@moduleUnboundedDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar)
      hY hD hB).symm := by
  change (@moduleUnboundedDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar)
    hY hD hB).symm ≪≫ Iso.refl _ = _
  exact Iso.trans_refl _

omit hY in
/-- The dense total-refinement unit is literally the original mixed identity unit. -/
theorem moduleUnboundedLeftUnitTotalRefinementDelta :
    (@moduleUnboundedDerivedRefinementComparison X Y f _
      (Hom.DenseCompactification.ofArrowEq (Category.id_comp f)
        (Hom.CompactifiedComposition.leftUnit C).composite) C
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C) Λ _ hX hB hD) =
    (@moduleUnboundedDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
      (𝟙 C.Xbar) (unboundedLeftUnitTowerTotalSquare C) Λ _ hX hB hD) := rfl

/-- The total image face is the same original mixed transition along the actual refinement. -/
theorem moduleUnboundedLeftUnitTotalMixedTransition :
    (@moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY
      (Hom.DenseCompactification.ofArrowEq (Category.id_comp f)
        (Hom.CompactifiedComposition.leftUnit C).composite) C
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C) hB hD) =
    CategoryTheory.imageComparison
      (L₁ := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hB)
      (L₂ := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD)
      (R₁ := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY hB)
      (R₂ := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar C.p hY hD)
      (F := @moduleUnboundedDerivedDirectImage Λ _ C.Xbar C.Xbar (𝟙 C.Xbar) hD hB)
      (@moduleUnboundedDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
        (𝟙 C.Xbar) (unboundedLeftUnitTowerTotalSquare C) Λ _ hX hB hD)
      (@moduleUnboundedDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar)
        hY hD hB).symm := by
  unfold moduleUnboundedCompactificationMixedTransition
  rw [moduleUnboundedLeftUnitTotalDirectImageIso, moduleUnboundedLeftUnitTotalRefinementDelta]
  rfl


end AlgebraicGeometry.Scheme.EtaleCohomology
