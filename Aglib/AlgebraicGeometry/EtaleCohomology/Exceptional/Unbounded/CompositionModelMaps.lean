/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMateNormalization
public import Aglib.CategoryTheory.Functor.ImageCompositionIsoFormula

/-! # Original components of the supplied-tower composition isomorphism

The canonical torsion comparison is identified with the already specified
global mixed mate. This is a formula for the accepted map, not a replacement
construction on isomorphic objects.
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
  (C : Hom.CompactifiedComposition f g)

/-- The local derived-category model on `ModuleSheaf C.first.Xbar Λ`. -/
local instance compositionMapsFirstModel : HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ)
      := firstModels C.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance compositionMapsTargetModel : HasDerivedCategory.{wG} (ModuleSheaf
      C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance compositionMapsTotalModel : HasDerivedCategory.{wFG} (ModuleSheaf
      C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite

/-- The exact open compositor used in the accepted supplied-tower construction. -/
def moduleUnboundedCompactifiedCompositionOpenIso :
    moduleUnboundedDerivedLowerShriek C.first.j Λ ⋙ moduleUnboundedDerivedLowerShriek
      C.middleOpen Λ ≅
      moduleUnboundedDerivedLowerShriek C.sourceCompactification.j Λ :=
  (moduleUnboundedDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
    eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ C.first_j_middleOpen)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [QuasiCompact f] in
/-- The original supplied-tower isomorphism retains its actual mixed-mate formula. -/
theorem moduleUnboundedCompactifiedCompositionIso_formula :
    ImageCompositionFormula
      (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
        C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
      (moduleUnboundedCompactifiedCompositionOpenIso f g Λ C)
      (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm
      (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ).hom :=
  imageCompositionFormula_of_originalIso
    (moduleUnboundedProperOpenComparisonIso Λ C.sourceCompactification.p C.first.p
      C.targetCompactification.j C.middleOpen C.isPullback_middleOpen N hN hΛ)
    (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
    (moduleUnboundedCompactifiedCompositionOpenIso f g Λ C)
    (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ)
    (moduleUnboundedProperOpenComparison_eq_mixedMate Λ C.sourceCompactification.p C.first.p
      C.targetCompactification.j C.middleOpen C.isPullback_middleOpen) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
