/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModelMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactifiedToDirectImageComposition
public import Aglib.CategoryTheory.Functor.CompositionToTargetTransport
public import Aglib.CategoryTheory.Functor.ImageCompositionToTargetAmbient

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
local instance unboundedToTargetCompositionFirstModel :
    HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) := firstModels C.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance unboundedToTargetCompositionSecondModel :
    HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance unboundedToTargetCompositionSourceModel :
    HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [QuasiCompact f] in
/-- The accepted original tower compositor commutes with the same canonical maps to R*. -/
theorem moduleUnboundedCompactifiedCompositionIso_toDirectImage :
    CompositionToTargetEquation
      (F := moduleUnboundedCompactificationFunctor f Λ C.first)
      (G := moduleUnboundedCompactificationFunctor g Λ C.targetCompactification)
      (H := moduleUnboundedCompactificationFunctor (f ≫ g) Λ C.composite)
      (R := moduleUnboundedDerivedDirectImage Λ f)
      (S := moduleUnboundedDerivedDirectImage Λ g)
      (T := moduleUnboundedDerivedDirectImage Λ (f ≫ g))
      (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
      (𝟭 (DerivedCategory (ModuleSheaf Y Λ)))
      (𝟭 (DerivedCategory (ModuleSheaf Z Λ)))
      (moduleUnboundedCompactificationToDirectImage f Λ C.first)
      (moduleUnboundedCompactificationToDirectImage g Λ C.targetCompactification)
      (moduleUnboundedCompactificationToDirectImage (f ≫ g) Λ C.composite)
      (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ)
      (moduleUnboundedDerivedDirectImageCompIso Λ g f).symm :=
  imageCompositionToTarget_ambient
    (moduleUnboundedLowerShriekToDirectImage Λ C.first.j)
    (moduleUnboundedLowerShriekToDirectImage Λ C.targetCompactification.j)
    (moduleUnboundedLowerShriekToDirectImage Λ C.sourceCompactification.j)
    (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
    (moduleUnboundedCompactifiedCompositionOpenIso f g Λ C)
    (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleUnboundedDerivedDirectImageOverIso Λ (f ≫ g) C.composite.p
      C.sourceCompactification.j C.composite.fac)
    (moduleUnboundedDerivedDirectImageOverIso Λ g C.targetCompactification.p
      C.targetCompactification.j C.targetCompactification.fac)
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.first.p C.first.j C.first.fac)
    (moduleUnboundedDerivedDirectImageCompIso Λ g f).symm
    (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso_formula f g Λ C N hN hΛ)
    (moduleUnboundedCompactifiedComposition_toDirectImage Λ C.first.j C.first.p
      C.targetCompactification.j C.targetCompactification.p C.middleOpen
      C.sourceCompactification.p C.sourceCompactification.j f g
      C.first_j_middleOpen C.first.fac C.targetCompactification.fac C.composite.fac
      C.isPullback_middleOpen.flip)
end AlgebraicGeometry.Scheme.EtaleCohomology
