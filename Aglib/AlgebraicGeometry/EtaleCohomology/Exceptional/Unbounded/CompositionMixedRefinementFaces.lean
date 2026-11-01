/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementFaces
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementHorizontal
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModelMaps

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
local instance compositionMixedFacesSourceModel : HasDerivedCategory.{wFG} (ModuleSheaf
      C.composite.Xbar Λ) := hC
/-- The local derived-category model on `ModuleSheaf D.composite.Xbar Λ`. -/
local instance compositionMixedFacesTargetModel : HasDerivedCategory.{wFGD} (ModuleSheaf
      D.composite.Xbar Λ) := hD

/-- The actual tower refinement satisfies the original abstract image cube.
Every face is supplied by a proved theorem for its original maps. -/
theorem moduleUnboundedCompactifiedCompositionMixedRefinementEquation :
    ImageCompositionRefinementEquation
      (moduleUnboundedDerivedRefinementComparison a.intermediate Λ)
      (moduleUnboundedDerivedRefinementComparison a.target Λ)
      (moduleUnboundedDerivedRefinementComparison a.source Λ)
      (moduleUnboundedProperOpenMate D.first.p D.middleOpen D.targetCompactification.j
      D.sourceCompactification.p D.isPullback_middleOpen.flip Λ)
      (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ D.middleOpen D.first.j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ
          (j := D.first.j ≫ D.middleOpen) (k := D.sourceCompactification.j)
          (show D.first.j ≫ D.middleOpen = D.sourceCompactification.j from
            D.first_j_middleOpen)))
      ((moduleUnboundedDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ
          (j := C.first.j ≫ C.middleOpen) (k := C.sourceCompactification.j)
          (show C.first.j ≫ C.middleOpen = C.sourceCompactification.j from
            C.first_j_middleOpen)))
      (moduleUnboundedDerivedRefinementDirectImageIso Λ a.intermediate)
      (moduleUnboundedDerivedRefinementDirectImageIso Λ a.target)
      (moduleUnboundedDerivedDirectImageCompIso Λ D.targetCompactification.p
        D.sourceCompactification.p).symm
      (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm
      (moduleUnboundedDerivedRefinementDirectImageIso Λ a.source) := by
  let σ := moduleUnboundedProperOpenMate a.intermediate.hom C.middleOpen D.middleOpen
      a.source.hom a.isPullback_middleOpen.flip Λ
  let r := moduleUnboundedProperOpenRefinementTargetIso Λ C.sourceCompactification.p
    D.sourceCompactification.p a.source.hom a.target.hom a.comm
  refine imageCompositionRefinementEquation _ _ _ _ _ σ _ _ _ _ r _ _ _ ?_ ?_ ?_
  · exact moduleUnboundedDerivedProperRefinementComparison_hComp_transport Λ
      C.first.j D.first.j C.middleOpen D.middleOpen a.intermediate.hom a.source.hom
      (Hom.DenseCompactification.isPullback_open a.intermediate) a.isPullback_middleOpen
      C.sourceCompactification.j D.sourceCompactification.j
      C.first_j_middleOpen D.first_j_middleOpen
      (Hom.DenseCompactification.isPullback_open a.source)
  · exact naturalPastedRectangle_contract_identitySource
      (moduleUnboundedDerivedAdjunction Λ (𝟙 Y)) (moduleUnboundedDerivedAdjunction Λ a.target.hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (𝟙 Y)
          C.targetCompactification.j D.targetCompactification.j a.target.hom
          (Hom.DenseCompactification.isPullback_open a.target).flip Λ).hom)
      (moduleUnboundedDerivedDirectImageIdIso Λ Y) (moduleUnboundedDerivedRefinementComparison
      a.target Λ)
      (moduleUnboundedDerivedProperRefinementComparison_identitySourceMate
        C.targetCompactification.j D.targetCompactification.j a.target.hom
        (Hom.DenseCompactification.isPullback_open a.target) Λ)
      _ _ _ _ _ _ rfl
      (moduleUnboundedProperOpenMate_refinement_rectangle Λ
        C.targetCompactification.j D.targetCompactification.j C.middleOpen D.middleOpen
        C.first.p D.first.p C.sourceCompactification.p D.sourceCompactification.p
        a.intermediate.hom a.source.hom a.target.hom
        C.isPullback_middleOpen D.isPullback_middleOpen a.isPullback_middleOpen
        (Hom.DenseCompactification.isPullback_open a.target)
        a.intermediate.base_fac a.comm)
  · exact moduleUnboundedDerivedDirectImageOverIso_rectangle Λ
      C.sourceCompactification.p D.sourceCompactification.p a.source.hom a.target.hom
      C.targetCompactification.p D.targetCompactification.p
      a.comm a.target.base_fac a.source.base_fac

end AlgebraicGeometry.Scheme.EtaleCohomology
