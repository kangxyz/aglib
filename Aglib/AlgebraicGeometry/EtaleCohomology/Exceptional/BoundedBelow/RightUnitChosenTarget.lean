/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionRightUnitRefinements
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelArrow

/-! # The original normalized target comparison in the chosen right-unit triangle -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification (f ≫ 𝟙 Y),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

/-- Arrow normalization and family transport retain the actual first-to-total refinement. -/
theorem moduleRightUnitChosenTargetSquare :
    moduleExceptionalDirectImagePlusTorsionCongr Λ hX hY (Category.comp_id f)
        compositeModels firstModels ≪≫
      moduleExceptionalDirectImagePlusTorsionIso f Λ
        (Hom.CompactifiedComposition.rightUnit C).first =
    moduleExceptionalDirectImagePlusTorsionIso (f ≫ 𝟙 Y) Λ
        (Hom.CompactifiedComposition.rightUnit C).composite ≪≫
      moduleCompactificationSingleTorsionTransition Λ
        (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C)
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite) := by
  let η := moduleExceptionalDirectImagePlusTorsionCongr Λ hX hY (Category.comp_id f)
    compositeModels firstModels
  let ρ := moduleExceptionalSingleTorsionValueIso f Λ
    (Hom.DenseCompactification.ofArrowEq (Category.comp_id f)
      (Hom.CompactifiedComposition.rightUnit C).composite)
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
  let t := moduleCompactificationSingleTorsionTransition Λ
    (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C)
    (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
  have hs := moduleExceptionalSingleTorsionValueIso_refinement f Λ
    (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C)
    (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
  have hs' := hs.trans (moduleExceptionalSingleTorsionValueIso_self f Λ
    (Hom.CompactifiedComposition.rightUnit C).first)
  have hg := moduleExceptionalSingleTorsionValueIso_congr Λ hX hY (Category.comp_id f)
    compositeModels (Hom.CompactifiedComposition.rightUnit C).composite
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite) firstModels
  have hg' := hg.trans (moduleExceptionalSingleTorsionValueIso_self (f ≫ 𝟙 Y) Λ
    (Hom.CompactifiedComposition.rightUnit C).composite)
  have hl := congrArg (fun z => η ≪≫ z) hs'.symm
  have hr := congrArg (fun z => z ≪≫ t) hg'
  exact hl.trans ((Iso.trans_assoc η ρ t).symm.trans hr)

end AlgebraicGeometry.Scheme.EtaleCohomology
