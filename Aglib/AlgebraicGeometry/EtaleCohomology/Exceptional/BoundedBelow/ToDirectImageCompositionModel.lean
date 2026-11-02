/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionModelMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompactifiedToDirectImageComposition
public import Aglib.CategoryTheory.Functor.CompositionToTargetTransport
public import Aglib.CategoryTheory.Functor.ImageCompositionToTargetRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters

/-! # Actual supplied-tower composition preserves the same canonical comparison -/
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
  (C : Hom.CompactifiedComposition f g)

/-- The local derived-category model on `ModuleSheaf C.first.Xbar Λ`. -/
local instance toDirectImageCompositionFirstModel :
    HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) := firstModels C.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance toDirectImageCompositionSecondModel :
    HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance toDirectImageCompositionSourceModel :
    HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite

omit [QuasiCompact f] in
/-- The accepted original tower compositor commutes with the same canonical maps to R*. -/
theorem moduleCompactifiedCompositionIso_toDirectImage :
    CompositionToTargetEquation
      (F := moduleCompactificationTorsionFunctor f Λ C.first)
      (G := moduleCompactificationTorsionFunctor g Λ C.targetCompactification)
      (H := moduleCompactificationTorsionFunctor (f ≫ g) Λ C.composite)
      (moduleTorsionCohomologyPlus X Λ).ι
      (moduleTorsionCohomologyPlus Y Λ).ι (moduleTorsionCohomologyPlus Z Λ).ι
      (moduleCompactificationToDirectImage f Λ C.first)
      (moduleCompactificationToDirectImage g Λ C.targetCompactification)
      (moduleCompactificationToDirectImage (f ≫ g) Λ C.composite)
      (moduleCompactifiedCompositionIso f g Λ C)
      (moduleDerivedDirectImageCompIso Λ g f).symm :=
  imageCompositionToTarget_restrict
    (moduleDerivedLowerShriekToDirectImage Λ C.first.j)
    (moduleDerivedLowerShriekToDirectImage Λ C.targetCompactification.j)
    (moduleDerivedLowerShriekToDirectImage Λ C.sourceCompactification.j)
    (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
      C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
    (moduleCompactifiedCompositionOpenIso f g Λ C)
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p C.sourceCompactification.p).symm
    (moduleDerivedDirectImageOverIso Λ (f ≫ g) C.composite.p
      C.sourceCompactification.j C.composite.fac)
    (moduleDerivedDirectImageOverIso Λ g C.targetCompactification.p
      C.targetCompactification.j C.targetCompactification.fac)
    (moduleDerivedDirectImageOverIso Λ f C.first.p C.first.j C.first.fac)
    (moduleDerivedDirectImageCompIso Λ g f).symm
    (moduleTorsionCohomologyPlus X Λ) (moduleTorsionCohomologyPlus Y Λ)
    (moduleTorsionCohomologyPlus Z Λ)
    (fun K => ((moduleCompactificationTorsionFunctor f Λ C.first).obj K).property)
    (fun K => ((moduleCompactificationTorsionFunctor g Λ C.targetCompactification).obj K).property)
    (fun K => ((moduleCompactificationTorsionFunctor (f ≫ g) Λ C.composite).obj K).property)
    (moduleCompactifiedCompositionIso f g Λ C)
    (moduleCompactifiedCompositionAmbientIso f g Λ C).hom rfl
    (moduleCompactifiedCompositionAmbientIso_formula f g Λ (C := C))
    (moduleCompactifiedComposition_toDirectImage Λ C.first.j C.first.p
      C.targetCompactification.j C.targetCompactification.p C.middleOpen
      C.sourceCompactification.p C.sourceCompactification.j f g
      C.first_j_middleOpen C.first.fac C.targetCompactification.fac C.composite.fac
      C.isPullback_middleOpen.flip)
end AlgebraicGeometry.Scheme.EtaleCohomology
