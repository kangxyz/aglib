/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionMixedRefinementFaces
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedModelTransition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonFormulas

/-! # Original refinement faces with six independent middle-model families

The horizontal original-unit equation, the vertical original-mate rectangle,
and structural proper-image coherence are proved suppliers, not extra premises.
Their common abstract equation keeps the native derived models opaque.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG wFD wGD wFGD

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  {C D : Hom.CompactifiedComposition f g} (a : C.Refinement D)
  [HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ)]
  [HasDerivedCategory.{wFD} (ModuleSheaf D.first.Xbar Λ)]
  [HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ)]
  [HasDerivedCategory.{wGD} (ModuleSheaf D.targetCompactification.Xbar Λ)]
  [hC : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ)]
  [hD : HasDerivedCategory.{wFGD} (ModuleSheaf D.sourceCompactification.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf C.composite.Xbar Λ`. -/
local instance compositionMixedWholeSourceModel : HasDerivedCategory.{wFG} (ModuleSheaf
      C.composite.Xbar Λ) := hC
/-- The local derived-category model on `ModuleSheaf D.composite.Xbar Λ`. -/
local instance compositionMixedWholeTargetModel : HasDerivedCategory.{wFGD} (ModuleSheaf
      D.composite.Xbar Λ) := hD

/-- The original direct-model cube assembles whole specified composition maps.
The supplied formulas identify the actual maps, not an assumed refinement square. -/
theorem moduleUnboundedCompactifiedCompositionMixedRefinement_whole
    (αD : moduleUnboundedDerivedLowerShriek D.first.j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ D.first.p ⋙
        moduleUnboundedDerivedLowerShriek D.targetCompactification.j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ D.targetCompactification.p ⟶
      moduleUnboundedDerivedLowerShriek D.sourceCompactification.j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ D.composite.p)
    (αC : moduleUnboundedDerivedLowerShriek C.first.j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ C.first.p ⋙
        moduleUnboundedDerivedLowerShriek C.targetCompactification.j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ C.targetCompactification.p ⟶
      moduleUnboundedDerivedLowerShriek C.sourceCompactification.j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ C.composite.p)
    (hD : ImageCompositionFormula
      (moduleUnboundedProperOpenMate D.first.p D.middleOpen D.targetCompactification.j
      D.sourceCompactification.p D.isPullback_middleOpen.flip Λ)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ D.middleOpen D.first.j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ
          (j := D.first.j ≫ D.middleOpen) (k := D.sourceCompactification.j)
          (show D.first.j ≫ D.middleOpen = D.sourceCompactification.j from
            D.first_j_middleOpen)))
      (moduleUnboundedDerivedDirectImageCompIso Λ D.targetCompactification.p
        D.sourceCompactification.p).symm αD)
    (hC : ImageCompositionFormula
      (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ
          (j := C.first.j ≫ C.middleOpen) (k := C.sourceCompactification.j)
          (show C.first.j ≫ C.middleOpen = C.sourceCompactification.j from
            C.first_j_middleOpen)))
      (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm αC) :
    ImageCompositionNaturalityEquation
      (moduleUnboundedCompactificationMixedTransition Λ a.intermediate)
      (moduleUnboundedCompactificationMixedTransition Λ a.target)
      (moduleUnboundedCompactificationMixedTransition Λ a.source) αD αC :=
  imageCompositionNaturalityEquation
    (moduleUnboundedDerivedRefinementComparison a.intermediate Λ)
    (moduleUnboundedDerivedRefinementComparison a.target Λ)
    (moduleUnboundedDerivedRefinementComparison a.source Λ)
    (moduleUnboundedProperOpenMate D.first.p D.middleOpen D.targetCompactification.j
      D.sourceCompactification.p D.isPullback_middleOpen.flip Λ)
    (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
    ((moduleUnboundedDerivedLowerShriekCompIso Λ D.middleOpen D.first.j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ
          (j := D.first.j ≫ D.middleOpen) (k := D.sourceCompactification.j)
          (show D.first.j ≫ D.middleOpen = D.sourceCompactification.j from
            D.first_j_middleOpen)))
    ((moduleUnboundedDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ
          (j := C.first.j ≫ C.middleOpen) (k := C.sourceCompactification.j)
          (show C.first.j ≫ C.middleOpen = C.sourceCompactification.j from
            C.first_j_middleOpen)))
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a.intermediate)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a.target)
    (moduleUnboundedDerivedDirectImageCompIso Λ D.targetCompactification.p
        D.sourceCompactification.p).symm
    (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a.source)
    _ _ _ αD αC
    (moduleUnboundedCompactifiedCompositionMixedRefinementEquation f g Λ a)
    (imageComparisonFormula _ _) (imageComparisonFormula _ _) (imageComparisonFormula _ _)
    hD hC

end AlgebraicGeometry.Scheme.EtaleCohomology
