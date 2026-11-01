/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ChosenImageComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionSingleModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsionRefinement

/-!
# Choice-independent composition of exceptional direct images

The original compactified composition maps are transported to the chosen native
bounded-below torsion functors. Their actual refinement cube and an actual common
refinement prove independence of the supplied compactification tower. This file
addresses binary composition; associativity and unit coherence are separate.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG wRaw wTop

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
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

variable (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (a : F ⟶ C.first) (hRaw : HasDerivedCategory.{wRaw} (ModuleSheaf F.Xbar Λ))

omit compositeModels in
/-- The original chosen source pair follows the actual first refinement. -/
theorem moduleExceptionalCompositionSingleSource :
    compositionPairIso
        (moduleExceptionalDirectImagePlusTorsionIso f Λ C.first)
        (moduleExceptionalDirectImagePlusTorsionIso g Λ C.targetCompactification) ≪≫
      Functor.isoWhiskerRight
        (moduleCompactificationSingleTorsionTransition Λ a hRaw (firstModels C.first))
        (moduleCompactificationTorsionFunctor g Λ C.targetCompactification) =
    compositionPairIso
      (moduleExceptionalSingleTorsionValueIso f Λ F hRaw)
      (moduleExceptionalSingleTorsionValueIso g Λ C.targetCompactification
        (secondModels C.targetCompactification)) := by
  have hf := moduleExceptionalSingleTorsionValueIso_refinement f Λ a hRaw (firstModels C.first)
  rw [moduleExceptionalSingleTorsionValueIso_self] at hf
  rw [moduleExceptionalSingleTorsionValueIso_self]
  exact compositionPairIso_first _ _ _ _ hf

end AlgebraicGeometry.Scheme.EtaleCohomology
