/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence

/-! # The original raw and mixed dense refinement maps are the same maps -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The general original raw transition specializes to the unchanged mixed-model
original dense transition; neither model is replaced. -/
theorem moduleRawDenseTransition_eq_mixed :
    moduleRawCompactificationTransition C.toCompactification D.toCompactification
      a.hom (Hom.DenseCompactification.isPullback_open a) a.base_fac Λ =
      moduleCompactificationMixedTransition Λ a :=
  congrArg (fun δ : moduleDerivedLowerShriek D.j Λ ⟶
      moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ a.hom =>
    Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (CategoryTheory.imageComparison δ (moduleDerivedRefinementDirectImageIso Λ a)))
    (moduleDerivedProperRefinementComparison_dense a Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
