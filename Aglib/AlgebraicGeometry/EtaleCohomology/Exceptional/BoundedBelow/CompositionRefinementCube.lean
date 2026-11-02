/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters
public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly
public import Aglib.CategoryTheory.Functor.CompositionChoice

/-! # The actual composition-tower refinement cube

The previously proved original faces are assembled before specializing the
native torsion-valued comparison. No desired refinement equality is assumed.
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
local instance compositionRefinementCubeFirstModelC :
    HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) :=
  firstModels C.first
/-- The local derived-category model on `ModuleSheaf D.first.Xbar Λ`. -/
local instance compositionRefinementCubeFirstModelD :
    HasDerivedCategory.{wF} (ModuleSheaf D.first.Xbar Λ) :=
  firstModels D.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance compositionRefinementCubeSecondModelC :
    HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf D.targetCompactification.Xbar Λ`. -/
local instance compositionRefinementCubeSecondModelD :
    HasDerivedCategory.{wG} (ModuleSheaf D.targetCompactification.Xbar Λ) :=
  secondModels D.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance compositionRefinementCubeCompositeModelC :
    HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite
/-- The local derived-category model on `ModuleSheaf D.sourceCompactification.Xbar Λ`. -/
local instance compositionRefinementCubeCompositeModelD :
    HasDerivedCategory.{wFG} (ModuleSheaf D.sourceCompactification.Xbar Λ) :=
  compositeModels D.composite

/-- The whole ambient square for the actual supplied-tower maps. -/
theorem moduleCompactifiedCompositionAmbientIso_refinement :
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
      (moduleCompactificationTransition Λ a.intermediate)
      (CategoryTheory.imageComparison (moduleDerivedRefinementComparison a.target Λ)
        (moduleDerivedRefinementDirectImageIso Λ a.target))
      (moduleCompactificationTransition Λ a.source)
      (moduleCompactifiedCompositionAmbientIso f g Λ D).hom
      (moduleCompactifiedCompositionAmbientIso f g Λ C).hom := by
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
      (moduleCompactifiedCompositionOpenIso f g Λ D))
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleCompactifiedCompositionOpenIso f g Λ C))
    (moduleDerivedRefinementDirectImageIso Λ a.intermediate)
    (moduleDerivedRefinementDirectImageIso Λ a.target)
    (moduleDerivedDirectImageCompIso Λ D.targetCompactification.p
      D.sourceCompactification.p).symm
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleDerivedRefinementDirectImageIso Λ a.source)
    _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · exact moduleCompactifiedCompositionRefinementEquation_torsionInput f g Λ a
  · exact moduleCompactificationTransition_formula f Λ a.intermediate
  · exact CategoryTheory.imageComparisonFormula (moduleDerivedRefinementComparison a.target Λ)
      (moduleDerivedRefinementDirectImageIso Λ a.target)
  · exact moduleCompactificationTransition_formula (f ≫ g) Λ a.source
  · exact moduleCompactifiedCompositionAmbientIso_formula f g Λ (C := D)
  · exact moduleCompactifiedCompositionAmbientIso_formula f g Λ (C := C)

include a in
/-- Actual canonical torsion-valued composition is compatible with every
original tower refinement. The inverse comparisons are the original transitions. -/
theorem moduleCompactifiedCompositionIso_refinement :
    (Functor.isoWhiskerRight
        (moduleCompactificationTorsionComparison f Λ C.first D.first).symm
        (moduleCompactificationTorsionFunctor g Λ D.targetCompactification) ≪≫
      Functor.isoWhiskerLeft (moduleCompactificationTorsionFunctor f Λ C.first)
        (moduleCompactificationTorsionComparison g Λ
          C.targetCompactification D.targetCompactification).symm) ≪≫
      moduleCompactifiedCompositionIso f g Λ C =
    moduleCompactifiedCompositionIso f g Λ D ≪≫
      (moduleCompactificationTorsionComparison (f ≫ g) Λ C.composite D.composite).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  change
    (moduleDerivedDirectImage Λ D.targetCompactification.p).map
      ((moduleDerivedLowerShriek D.targetCompactification.j Λ).map
        (((moduleCompactificationTorsionComparison f Λ C.first D.first).inv.app K).hom)) ≫
      ((moduleCompactificationTorsionComparison g Λ C.targetCompactification
        D.targetCompactification).inv.app
          ((moduleCompactificationTorsionFunctor f Λ C.first).obj K)).hom ≫
      (moduleCompactifiedCompositionAmbientIso f g Λ C).hom.app K =
    (moduleCompactifiedCompositionAmbientIso f g Λ D).hom.app K ≫
      ((moduleCompactificationTorsionComparison (f ≫ g) Λ C.composite D.composite).inv.app K).hom
  rw [moduleCompactificationTorsionComparison_inv_refinement f Λ a.intermediate,
    moduleCompactificationTorsionComparison_inv_refinement g Λ a.target,
    moduleCompactificationTorsionComparison_inv_refinement (f ≫ g) Λ a.source]
  have h := congrArg (fun t => t.app K)
    (moduleCompactifiedCompositionAmbientIso_refinement f g Λ a)
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
