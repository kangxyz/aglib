/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.ToDirectImageCompositionModel

/-! # The chosen compositor preserves the same canonical exceptional-to-ordinary map -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wG wFG
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

/-- Computed through any supplied tower, the original chosen compositor commutes with
exactly the same canonical maps and the original ordinary direct-image compositor. -/
theorem moduleExceptionalToDirectImage_composition_model
    (C : Hom.CompactifiedComposition f g) :
    CompositionToTargetEquation
      (F := moduleExceptionalDirectImagePlusTorsion f Λ)
      (G := moduleExceptionalDirectImagePlusTorsion g Λ)
      (H := moduleExceptionalDirectImagePlusTorsion (f ≫ g) Λ)
      (moduleTorsionCohomologyPlus X Λ).ι
      (moduleTorsionCohomologyPlus Y Λ).ι (moduleTorsionCohomologyPlus Z Λ).ι
      (moduleExceptionalToDirectImage f Λ) (moduleExceptionalToDirectImage g Λ)
      (moduleExceptionalToDirectImage (f ≫ g) Λ)
      (moduleExceptionalCompositionIso f g Λ)
      (moduleDerivedDirectImageCompIso Λ g f).symm :=
  compositionToTarget_transport
    (F := moduleExceptionalDirectImagePlusTorsion f Λ)
    (G := moduleExceptionalDirectImagePlusTorsion g Λ)
    (H := moduleExceptionalDirectImagePlusTorsion (f ≫ g) Λ)
    (Fm := moduleCompactificationTorsionFunctor f Λ C.first)
    (Gm := moduleCompactificationTorsionFunctor g Λ C.targetCompactification)
    (Hm := moduleCompactificationTorsionFunctor (f ≫ g) Λ C.composite)
    (moduleTorsionCohomologyPlus X Λ).ι
    (moduleTorsionCohomologyPlus Y Λ).ι (moduleTorsionCohomologyPlus Z Λ).ι
    (moduleExceptionalToDirectImage f Λ) (moduleExceptionalToDirectImage g Λ)
    (moduleExceptionalToDirectImage (f ≫ g) Λ)
    (moduleCompactificationToDirectImage f Λ C.first)
    (moduleCompactificationToDirectImage g Λ C.targetCompactification)
    (moduleCompactificationToDirectImage (f ≫ g) Λ C.composite)
    (moduleExceptionalCompositionIso f g Λ) (moduleCompactifiedCompositionIso f g Λ C)
    (moduleDerivedDirectImageCompIso Λ g f).symm
    (moduleExceptionalDirectImagePlusTorsionIso f Λ C.first)
    (moduleExceptionalDirectImagePlusTorsionIso g Λ C.targetCompactification)
    (moduleExceptionalDirectImagePlusTorsionIso (f ≫ g) Λ C.composite)
    (moduleExceptionalToDirectImage_model f Λ C.first)
    (moduleExceptionalToDirectImage_model g Λ C.targetCompactification)
    (moduleExceptionalToDirectImage_model (f ≫ g) Λ C.composite)
    (moduleExceptionalCompositionIso_comparison f g Λ C)
    (moduleCompactifiedCompositionIso_toDirectImage f g Λ C)
end AlgebraicGeometry.Scheme.EtaleCohomology
