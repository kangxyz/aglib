/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionMixedRefinementFaces
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonFormulas
public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly
public import Aglib.CategoryTheory.Functor.ImageCompositionRestriction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence

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
local instance instMixedWholeCompositeModelC :
    HasDerivedCategory.{wFG} (ModuleSheaf C.composite.Xbar Λ) := hC
/-- The local derived-category model on `ModuleSheaf D.composite.Xbar Λ`. -/
local instance instMixedWholeCompositeModelD :
    HasDerivedCategory.{wFGD} (ModuleSheaf D.composite.Xbar Λ) := hD

/-- Source restriction preserves the proved whole original refinement cube. -/
theorem moduleCompactifiedCompositionMixedRefinementEquation_torsionInput :
    ImageCompositionRefinementEquation
      (K₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek D.first.j Λ)
      (K₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek C.first.j Λ)
      (J₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek D.sourceCompactification.j Λ)
      (J₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek C.sourceCompactification.j Λ)
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedRefinementComparison a.intermediate Λ))
      (moduleDerivedRefinementComparison a.target Λ)
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedRefinementComparison a.source Λ))
      (moduleProperOpenMate Λ D.targetCompactification.j D.middleOpen
        D.first.p D.sourceCompactification.p D.isPullback_middleOpen.flip)
      (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
        C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        ((moduleDerivedLowerShriekCompIso Λ D.middleOpen D.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := D.first.j ≫ D.middleOpen) (g := D.sourceCompactification.j)
          D.first_j_middleOpen)))
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        ((moduleDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := C.first.j ≫ C.middleOpen) (g := C.sourceCompactification.j)
          C.first_j_middleOpen)))
      (moduleDerivedRefinementDirectImageIso Λ a.intermediate)
      (moduleDerivedRefinementDirectImageIso Λ a.target)
      (moduleDerivedDirectImageCompIso Λ D.targetCompactification.p
        D.sourceCompactification.p).symm
      (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm
      (moduleDerivedRefinementDirectImageIso Λ a.source) :=
  imageCompositionRefinementEquation_whiskerLeft
    (moduleDerivedRefinementComparison a.intermediate Λ)
    (moduleDerivedRefinementComparison a.target Λ)
    (moduleDerivedRefinementComparison a.source Λ)
    (moduleProperOpenMate Λ D.targetCompactification.j D.middleOpen
      D.first.p D.sourceCompactification.p D.isPullback_middleOpen.flip)
    (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
      C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
    ((moduleDerivedLowerShriekCompIso Λ D.middleOpen D.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := D.first.j ≫ D.middleOpen) (g := D.sourceCompactification.j)
          D.first_j_middleOpen))
    ((moduleDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := C.first.j ≫ C.middleOpen) (g := C.sourceCompactification.j)
          C.first_j_middleOpen))
    (moduleDerivedRefinementDirectImageIso Λ a.intermediate)
    (moduleDerivedRefinementDirectImageIso Λ a.target)
    (moduleDerivedDirectImageCompIso Λ D.targetCompactification.p
      D.sourceCompactification.p).symm
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleDerivedRefinementDirectImageIso Λ a.source)
    (moduleTorsionCohomologyPlus X Λ).ι
    (moduleCompactifiedCompositionMixedRefinementEquation f g Λ a)

/-- The whole ambient square for the actual supplied-tower maps. -/
theorem moduleCompactifiedCompositionMixedRefinement_whole
    (αD : ((moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek D.first.j Λ) ⋙
        moduleDerivedDirectImage Λ D.first.p ⋙
        moduleDerivedLowerShriek D.targetCompactification.j Λ ⋙
        moduleDerivedDirectImage Λ D.targetCompactification.p ⟶
      ((moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek D.sourceCompactification.j Λ) ⋙
        moduleDerivedDirectImage Λ D.composite.p)
    (αC : ((moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek C.first.j Λ) ⋙
        moduleDerivedDirectImage Λ C.first.p ⋙
        moduleDerivedLowerShriek C.targetCompactification.j Λ ⋙
        moduleDerivedDirectImage Λ C.targetCompactification.p ⟶
      ((moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek C.sourceCompactification.j Λ) ⋙
        moduleDerivedDirectImage Λ C.composite.p)
    (hD : ImageCompositionFormula
      (moduleProperOpenMate Λ D.targetCompactification.j D.middleOpen
        D.first.p D.sourceCompactification.p D.isPullback_middleOpen.flip)
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        ((moduleDerivedLowerShriekCompIso Λ D.middleOpen D.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := D.first.j ≫ D.middleOpen) (g := D.sourceCompactification.j)
          D.first_j_middleOpen)))
      (moduleDerivedDirectImageCompIso Λ D.targetCompactification.p
        D.sourceCompactification.p).symm αD)
    (hC : ImageCompositionFormula
      (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
        C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        ((moduleDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := C.first.j ≫ C.middleOpen) (g := C.sourceCompactification.j)
          C.first_j_middleOpen)))
      (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm αC) :
    ImageCompositionNaturalityEquation
      (K₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek D.first.j Λ)
      (K₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek C.first.j Λ)
      (J₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek D.sourceCompactification.j Λ)
      (J₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek C.sourceCompactification.j Λ)
      (S₀ := moduleDerivedDirectImage Λ D.composite.p)
      (S₁ := moduleDerivedDirectImage Λ C.composite.p)
      (Q₀ := moduleDerivedDirectImage Λ D.first.p)
      (Q₁ := moduleDerivedDirectImage Λ C.first.p)
      (I₀ := moduleDerivedLowerShriek D.targetCompactification.j Λ)
      (I₁ := moduleDerivedLowerShriek C.targetCompactification.j Λ)
      (P₀ := moduleDerivedDirectImage Λ D.targetCompactification.p)
      (P₁ := moduleDerivedDirectImage Λ C.targetCompactification.p)
      (moduleCompactificationMixedTransition Λ a.intermediate)
      (CategoryTheory.imageComparison (moduleDerivedRefinementComparison a.target Λ)
        (moduleDerivedRefinementDirectImageIso Λ a.target))
      (moduleCompactificationMixedTransition Λ a.source)
      αD
      αC := by
  refine imageCompositionNaturalityEquation
    (K₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek D.first.j Λ)
    (K₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek C.first.j Λ)
    (J₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
      moduleDerivedLowerShriek D.sourceCompactification.j Λ)
    (J₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙
      moduleDerivedLowerShriek C.sourceCompactification.j Λ)
    (L₀ := moduleDerivedLowerShriek D.middleOpen Λ)
    (L₁ := moduleDerivedLowerShriek C.middleOpen Λ)
    (Q₀ := moduleDerivedDirectImage Λ D.first.p)
    (Q₁ := moduleDerivedDirectImage Λ C.first.p)
    (I₀ := moduleDerivedLowerShriek D.targetCompactification.j Λ)
    (I₁ := moduleDerivedLowerShriek C.targetCompactification.j Λ)
    (R₀ := moduleDerivedDirectImage Λ D.sourceCompactification.p)
    (R₁ := moduleDerivedDirectImage Λ C.sourceCompactification.p)
    (P₀ := moduleDerivedDirectImage Λ D.targetCompactification.p)
    (P₁ := moduleDerivedDirectImage Λ C.targetCompactification.p)
    (S₀ := moduleDerivedDirectImage Λ D.composite.p)
    (S₁ := moduleDerivedDirectImage Λ C.composite.p)
    (F := moduleDerivedDirectImage Λ a.intermediate.hom)
    (G := moduleDerivedDirectImage Λ a.source.hom)
    (H := moduleDerivedDirectImage Λ a.target.hom)
    (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedRefinementComparison a.intermediate Λ))
    (moduleDerivedRefinementComparison a.target Λ)
    (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedRefinementComparison a.source Λ))
    (moduleProperOpenMate Λ D.targetCompactification.j D.middleOpen
      D.first.p D.sourceCompactification.p D.isPullback_middleOpen.flip)
    (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
      C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      ((moduleDerivedLowerShriekCompIso Λ D.middleOpen D.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := D.first.j ≫ D.middleOpen) (g := D.sourceCompactification.j)
          D.first_j_middleOpen)))
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      ((moduleDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ
          (f := C.first.j ≫ C.middleOpen) (g := C.sourceCompactification.j)
          C.first_j_middleOpen)))
    (moduleDerivedRefinementDirectImageIso Λ a.intermediate)
    (moduleDerivedRefinementDirectImageIso Λ a.target)
    (moduleDerivedDirectImageCompIso Λ D.targetCompactification.p
      D.sourceCompactification.p).symm
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleDerivedRefinementDirectImageIso Λ a.source)
    _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · exact moduleCompactifiedCompositionMixedRefinementEquation_torsionInput f g Λ a
  · exact CategoryTheory.imageComparisonFormula_whiskerLeft
      (moduleDerivedRefinementComparison a.intermediate Λ)
      (moduleDerivedRefinementDirectImageIso Λ a.intermediate)
      (moduleTorsionCohomologyPlus X Λ).ι
  · exact CategoryTheory.imageComparisonFormula (moduleDerivedRefinementComparison a.target Λ)
      (moduleDerivedRefinementDirectImageIso Λ a.target)
  · exact CategoryTheory.imageComparisonFormula_whiskerLeft
      (moduleDerivedRefinementComparison a.source Λ)
      (moduleDerivedRefinementDirectImageIso Λ a.source)
      (moduleTorsionCohomologyPlus X Λ).ι
  · exact hD
  · exact hC

end AlgebraicGeometry.Scheme.EtaleCohomology
