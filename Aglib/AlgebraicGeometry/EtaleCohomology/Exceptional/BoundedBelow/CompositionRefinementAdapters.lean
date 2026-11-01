/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementFaces
public import Aglib.CategoryTheory.Functor.ImageCompositionRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonFormulas

/-! # Whole original input predicates for the native torsion composition cube

Source restriction and original component factorizations cross named predicate
boundaries before assembling the native whole square. The original maps and
independent derived model families are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wY wZ wF wG wFG

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  {C D : Hom.CompactifiedComposition f g} (a : C.Refinement D)

/-- The local derived-category model on `ModuleSheaf C.first.Xbar Λ`. -/
local instance compositionRefinementAdaptersFirstModelC :
    HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) :=
  firstModels C.first
/-- The local derived-category model on `ModuleSheaf D.first.Xbar Λ`. -/
local instance compositionRefinementAdaptersFirstModelD :
    HasDerivedCategory.{wF} (ModuleSheaf D.first.Xbar Λ) :=
  firstModels D.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance compositionRefinementAdaptersSecondModelC :
    HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf D.targetCompactification.Xbar Λ`. -/
local instance compositionRefinementAdaptersSecondModelD :
    HasDerivedCategory.{wG} (ModuleSheaf D.targetCompactification.Xbar Λ) :=
  secondModels D.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance compositionRefinementAdaptersCompositeModelC :
    HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite
/-- The local derived-category model on `ModuleSheaf D.sourceCompactification.Xbar Λ`. -/
local instance compositionRefinementAdaptersCompositeModelD :
    HasDerivedCategory.{wFG} (ModuleSheaf D.sourceCompactification.Xbar Λ) :=
  compositeModels D.composite

/-- Source restriction preserves the proved whole original refinement cube. -/
theorem moduleCompactifiedCompositionRefinementEquation_torsionInput :
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
        (moduleCompactifiedCompositionOpenIso f g Λ D))
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleCompactifiedCompositionOpenIso f g Λ C))
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
    (moduleCompactifiedCompositionOpenIso f g Λ D)
    (moduleCompactifiedCompositionOpenIso f g Λ C)
    (moduleDerivedRefinementDirectImageIso Λ a.intermediate)
    (moduleDerivedRefinementDirectImageIso Λ a.target)
    (moduleDerivedDirectImageCompIso Λ D.targetCompactification.p
      D.sourceCompactification.p).symm
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleDerivedRefinementDirectImageIso Λ a.source)
    (moduleTorsionCohomologyPlus X Λ).ι
    (moduleCompactifiedCompositionRefinementEquation f g Λ a)

/-- The original transition retains its whole factorization predicate. -/
theorem moduleCompactificationTransition_formula
    {E F : Hom.DenseCompactification f} (r : E ⟶ F) :
    ImageRefinementFormula
      (L₀ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek F.j Λ)
      (L₁ := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek E.j Λ)
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedRefinementComparison r Λ))
      (moduleDerivedRefinementDirectImageIso Λ r)
      (moduleCompactificationTransition Λ r) :=
  CategoryTheory.imageComparisonFormula_whiskerLeft
    (moduleDerivedRefinementComparison r Λ) (moduleDerivedRefinementDirectImageIso Λ r)
    (moduleTorsionCohomologyPlus X Λ).ι

omit [QuasiCompact f] in
/-- The accepted original composition map supplies the exact whole input formula. -/
theorem moduleCompactifiedCompositionAmbientIso_formula :
    ImageCompositionFormula
      (K := (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek C.first.j Λ)
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek C.sourceCompactification.j Λ)
      (L := moduleDerivedLowerShriek C.middleOpen Λ)
      (Q := moduleDerivedDirectImage Λ C.first.p)
      (I := moduleDerivedLowerShriek C.targetCompactification.j Λ)
      (R := moduleDerivedDirectImage Λ C.sourceCompactification.p)
      (P := moduleDerivedDirectImage Λ C.targetCompactification.p)
      (S := moduleDerivedDirectImage Λ C.composite.p)
      (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
        C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleCompactifiedCompositionOpenIso f g Λ C))
      (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm
      (moduleCompactifiedCompositionAmbientIso f g Λ C).hom :=
  moduleCompactifiedCompositionAmbientIso_hom_app f g Λ C

end AlgebraicGeometry.Scheme.EtaleCohomology
