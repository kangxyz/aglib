/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelArrow
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsionRefinement
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionArrowTotal

/-! # Chosen total-arrow transport agrees with the original triple refinement

The left and right total families remain independent. The comparison uses the
actual factored refinement to the arrow-transported right compactification.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wW wL wR wT
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  [CompactSpace W] [QuasiSeparatedSpace W]
  [IsSeparated f] [LocallyOfFiniteType f]
  [IsSeparated g] [LocallyOfFiniteType g]
  [IsSeparated h] [LocallyOfFiniteType h]
  (T : Hom.TripleCompactifiedComposition f g h) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  (leftModels : ∀ C : Hom.DenseCompactification ((f ≫ g) ≫ h),
    HasDerivedCategory.{wL} (ModuleSheaf C.Xbar Λ))
  (rightModels : ∀ C : Hom.DenseCompactification (f ≫ (g ≫ h)),
    HasDerivedCategory.{wR} (ModuleSheaf C.Xbar Λ))
  (hT : HasDerivedCategory.{wT} (ModuleSheaf T.first.Xbar Λ))

/-- The inverse actual total refinement realizes the original chosen arrow congruence. -/
theorem moduleTripleChosenTotalComparison :
    moduleExceptionalSingleTorsionValueIso (models := leftModels)
        ((f ≫ g) ≫ h) Λ T.leftOuter.composite hT ≪≫
      (moduleCompactificationSingleTorsionTransition Λ T.totalArrowRefinement hT hT).symm =
    moduleExceptionalDirectImagePlusTorsionCongr Λ hX hW (Category.assoc f g h)
        leftModels rightModels ≪≫
      moduleExceptionalSingleTorsionValueIso (models := rightModels)
        (f ≫ (g ≫ h)) Λ T.rightOuter.composite hT := by
  have hr := moduleExceptionalSingleTorsionValueIso_refinement
    (models := leftModels) ((f ≫ g) ≫ h) Λ T.totalArrowRefinement hT hT
  have hc := moduleExceptionalSingleTorsionValueIso_congr Λ hX hW
    (Category.assoc f g h) leftModels T.rightTotalArrowTransport hT rightModels
  change moduleExceptionalDirectImagePlusTorsionCongr Λ hX hW (Category.assoc f g h)
      leftModels rightModels ≪≫
      moduleExceptionalSingleTorsionValueIso (models := rightModels)
        (f ≫ (g ≫ h)) Λ T.rightOuter.composite hT =
    moduleExceptionalSingleTorsionValueIso (models := leftModels)
      ((f ≫ g) ≫ h) Λ T.rightTotalArrowTransport hT at hc
  have hr' := congrArg (fun z => z ≪≫
    (moduleCompactificationSingleTorsionTransition Λ T.totalArrowRefinement hT hT).symm) hr
  refine Eq.trans ?_ hc.symm
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hr'.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
