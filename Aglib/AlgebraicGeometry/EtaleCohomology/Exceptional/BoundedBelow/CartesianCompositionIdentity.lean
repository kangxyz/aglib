/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Diagram
public import Aglib.CategoryTheory.Functor.ImageComparisonRestriction

/-! # The unchanged image faces in a Cartesian first-presentation comparison -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  (C : Hom.DenseCompactification f)
  [hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]

/-- The original identity refinement is the identity image map before torsion restriction. -/
theorem moduleDerivedCompactificationImageIdentity :
    CategoryTheory.imageComparison (moduleDerivedRefinementComparison (𝟙 C) Λ)
      (moduleDerivedRefinementDirectImageIso Λ (𝟙 C)) =
      𝟙 (moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p) :=
  CategoryTheory.imageComparison_id (moduleDerivedRefinementComparison (𝟙 C) Λ)
    (moduleDerivedDirectImageIdIso Λ C.Xbar) (moduleDerivedRefinementDirectImageIso Λ (𝟙 C))
    (moduleDerivedRefinementComparison_id Λ C) (moduleDerivedRefinementDirectImageIso_id Λ C)

/-- The same actual identity remains unchanged on the original torsion source. -/
theorem moduleDerivedCompactificationImageIdentity_torsion :
    Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (CategoryTheory.imageComparison (moduleDerivedRefinementComparison (𝟙 C) Λ)
        (moduleDerivedRefinementDirectImageIso Λ (𝟙 C))) =
      𝟙 ((moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek C.j Λ ⋙
        moduleDerivedDirectImage Λ C.p) := by
  have h := congrArg (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι)
    (moduleDerivedCompactificationImageIdentity Λ C)
  exact h.trans (Functor.whiskerLeft_id' _)

end AlgebraicGeometry.Scheme.EtaleCohomology
