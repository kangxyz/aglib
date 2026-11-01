/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementFaces
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationIndependence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonFormulas
public import Aglib.CategoryTheory.Functor.CompositionIsoNaturality

/-! # The proved original faces of an actual composition-tower refinement

The horizontal original-unit equation, the vertical original-mate rectangle,
and structural proper-image coherence are proved suppliers, not extra premises.
Their common abstract equation keeps the native derived models opaque.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

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
local instance compositionCubeModel0 : HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) :=
      firstModels C.first
/-- The local derived-category model on `ModuleSheaf D.first.Xbar Λ`. -/
local instance compositionCubeModel1 : HasDerivedCategory.{wF} (ModuleSheaf D.first.Xbar Λ) :=
      firstModels D.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance compositionCubeModel2 : HasDerivedCategory.{wG} (ModuleSheaf
      C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf D.targetCompactification.Xbar Λ`. -/
local instance compositionCubeModel3 : HasDerivedCategory.{wG} (ModuleSheaf
      D.targetCompactification.Xbar Λ) :=
  secondModels D.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance compositionCubeModel4 : HasDerivedCategory.{wFG} (ModuleSheaf
      C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite
/-- The local derived-category model on `ModuleSheaf D.sourceCompactification.Xbar Λ`. -/
local instance compositionCubeModel5 : HasDerivedCategory.{wFG} (ModuleSheaf
      D.sourceCompactification.Xbar Λ) :=
  compositeModels D.composite

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original supplied comparisons satisfy the whole tower refinement square. -/
theorem moduleUnboundedCompactifiedCompositionIso_refinement_equation :
    ImageCompositionNaturalityEquation
      (moduleUnboundedCompactificationTransition Λ a.intermediate)
      (moduleUnboundedCompactificationTransition Λ a.target)
      (moduleUnboundedCompactificationTransition Λ a.source)
      (moduleUnboundedCompactifiedCompositionIso f g Λ D N hN hΛ).hom
      (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ).hom := by
  exact imageCompositionNaturalityEquation
    (moduleUnboundedDerivedRefinementComparison a.intermediate Λ)
    (moduleUnboundedDerivedRefinementComparison a.target Λ)
    (moduleUnboundedDerivedRefinementComparison a.source Λ)
    (moduleUnboundedProperOpenMate D.first.p D.middleOpen D.targetCompactification.j
      D.sourceCompactification.p D.isPullback_middleOpen.flip Λ)
    (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
    (moduleUnboundedCompactifiedCompositionOpenIso f g Λ D)
    (moduleUnboundedCompactifiedCompositionOpenIso f g Λ C)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a.intermediate)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a.target)
    (moduleUnboundedDerivedDirectImageCompIso Λ D.targetCompactification.p
      D.sourceCompactification.p).symm
    (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a.source)
    _ _ _ _ _
    (moduleUnboundedCompactifiedCompositionRefinementEquation f g Λ a)
    (imageComparisonFormula _ _) (imageComparisonFormula _ _) (imageComparisonFormula _ _)
    (moduleUnboundedCompactifiedCompositionIso_formula f g Λ D N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso_formula f g Λ C N hN hΛ)

include a in
/-- Canonical binary comparison commutes with every actual tower refinement. -/
theorem moduleUnboundedCompactifiedCompositionIso_refinement :
    compositionPairIso
        (moduleUnboundedCompactificationComparison f Λ N hN hΛ C.first D.first).symm
        (moduleUnboundedCompactificationComparison g Λ N hN hΛ
          C.targetCompactification D.targetCompactification).symm ≪≫
      moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ =
    moduleUnboundedCompactifiedCompositionIso f g Λ D N hN hΛ ≪≫
      (moduleUnboundedCompactificationComparison (f ≫ g) Λ N hN hΛ
        C.composite D.composite).symm := by
  rw [moduleUnboundedCompactificationComparison_refinement f Λ N hN hΛ a.intermediate,
    moduleUnboundedCompactificationComparison_refinement g Λ N hN hΛ a.target,
    moduleUnboundedCompactificationComparison_refinement (f ≫ g) Λ N hN hΛ a.source]
  exact compositionIsoNaturality_of_originalMaps
    (moduleUnboundedCompactificationTransitionIso f Λ N hN hΛ a.intermediate)
    (moduleUnboundedCompactificationTransitionIso g Λ N hN hΛ a.target)
    (moduleUnboundedCompactificationTransitionIso (f ≫ g) Λ N hN hΛ a.source)
    (moduleUnboundedCompactifiedCompositionIso f g Λ D N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ)
    (moduleUnboundedCompactificationTransition Λ a.intermediate)
    (moduleUnboundedCompactificationTransition Λ a.target)
    (moduleUnboundedCompactificationTransition Λ a.source)
    rfl rfl rfl
    (moduleUnboundedCompactifiedCompositionIso_refinement_equation f g Λ a N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
