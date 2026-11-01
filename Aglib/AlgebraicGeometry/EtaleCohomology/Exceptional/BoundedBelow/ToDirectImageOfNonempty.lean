/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SuppliedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.ToDirectImageNaturality

/-! # The same canonical comparison for a supplied compactifiable morphism -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The original model map, selected by the same supplied compactification as the functor. -/
def moduleExceptionalToDirectImageOfNonempty :
    moduleExceptionalDirectImagePlusOfNonempty f Λ ⟶
      (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  moduleCompactificationToDirectImage f Λ (moduleExceptionalSuppliedCompactification f)

/-- The same map is computed through every original compactification, with no qcqs base premise. -/
theorem moduleExceptionalToDirectImageOfNonempty_model (C : Hom.DenseCompactification f) :
    TargetComparisonEquation (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C).hom
      (moduleCompactificationToDirectImage f Λ C)
      (moduleExceptionalToDirectImageOfNonempty f Λ) :=
  moduleCompactificationToDirectImage_comparison f Λ (moduleExceptionalSuppliedCompactification f) C
end AlgebraicGeometry.Scheme.EtaleCohomology
