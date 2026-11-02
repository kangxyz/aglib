/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementHorizontal
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionModelMaps

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
local instance : HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) := firstModels C.first
/-- The local derived-category model on `ModuleSheaf D.first.Xbar Λ`. -/
local instance : HasDerivedCategory.{wF} (ModuleSheaf D.first.Xbar Λ) := firstModels D.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf D.targetCompactification.Xbar Λ`. -/
local instance : HasDerivedCategory.{wG} (ModuleSheaf D.targetCompactification.Xbar Λ) :=
  secondModels D.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite
/-- The local derived-category model on `ModuleSheaf D.sourceCompactification.Xbar Λ`. -/
local instance : HasDerivedCategory.{wFG} (ModuleSheaf D.sourceCompactification.Xbar Λ) :=
  compositeModels D.composite

/-- The actual tower refinement satisfies the original abstract image cube.
Every face is supplied by a proved theorem for its original maps. -/
theorem moduleCompactifiedCompositionRefinementEquation :
    ImageCompositionRefinementEquation
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
      (moduleDerivedRefinementDirectImageIso Λ a.source) := by
  let σ := moduleProperOpenMate Λ D.middleOpen C.middleOpen a.intermediate.hom a.source.hom
    a.isPullback_middleOpen.flip
  let r := moduleProperOpenRefinementTargetIso Λ C.sourceCompactification.p
    D.sourceCompactification.p a.source.hom a.target.hom a.comm
  refine imageCompositionRefinementEquation _ _ _ _ _ σ _ _ _ _ r _ _ _ ?_ ?_ ?_
  · exact moduleDerivedProperRefinementComparison_hComp_transport Λ
      C.first.j D.first.j C.middleOpen D.middleOpen a.intermediate.hom a.source.hom
      (Hom.DenseCompactification.isPullback_open a.intermediate) a.isPullback_middleOpen
      C.sourceCompactification.j D.sourceCompactification.j
      C.first_j_middleOpen D.first_j_middleOpen
      (Hom.DenseCompactification.isPullback_open a.source)
  · exact naturalPastedRectangle_contract_identitySource
      (moduleDerivedAdjunction Λ (𝟙 Y)) (moduleDerivedAdjunction Λ a.target.hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 Y)
          C.targetCompactification.j D.targetCompactification.j a.target.hom
          (Hom.DenseCompactification.isPullback_open a.target).flip Λ).hom)
      (moduleDerivedDirectImageIdIso Λ Y) (moduleDerivedRefinementComparison a.target Λ)
      (moduleDerivedRefinementComparison_identitySourceMate a.target Λ)
      _ _ _ _ _ _ rfl
      (moduleProperOpenMate_refinement_rectangle Λ
        C.targetCompactification.j D.targetCompactification.j C.middleOpen D.middleOpen
        C.first.p D.first.p C.sourceCompactification.p D.sourceCompactification.p
        a.intermediate.hom a.source.hom a.target.hom
        C.isPullback_middleOpen D.isPullback_middleOpen a.isPullback_middleOpen
        (Hom.DenseCompactification.isPullback_open a.target)
        a.intermediate.base_fac a.comm)
  · exact moduleDerivedDirectImageOverIso_rectangle Λ
      C.sourceCompactification.p D.sourceCompactification.p a.source.hom a.target.hom
      C.targetCompactification.p D.targetCompactification.p
      a.comm a.target.base_fac a.source.base_fac

end AlgebraicGeometry.Scheme.EtaleCohomology
