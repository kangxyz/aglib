/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationDiagram
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

/-- The original identity refinement is the identity image map before identity precomposition. -/
theorem moduleUnboundedDerivedCompactificationImageIdentity :
    CategoryTheory.imageComparison (moduleUnboundedDerivedRefinementComparison (𝟙 C) Λ)
      (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C)) =
      𝟙 (moduleUnboundedDerivedLowerShriek C.j Λ ⋙ moduleUnboundedDerivedDirectImage Λ C.p) :=
  CategoryTheory.imageComparison_id (moduleUnboundedDerivedRefinementComparison (𝟙 C) Λ)
    (moduleUnboundedDerivedDirectImageIdIso Λ C.Xbar)
      (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C))
    (moduleUnboundedDerivedRefinementComparison_id Λ C)
      (moduleUnboundedDerivedRefinementDirectImageIso_id Λ C)

/-- The same actual identity remains unchanged on the original unbounded source. -/
theorem moduleUnboundedDerivedCompactificationImageIdentity_identityWhisker :
    Functor.whiskerLeft (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
      (CategoryTheory.imageComparison (moduleUnboundedDerivedRefinementComparison (𝟙 C) Λ)
        (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C))) =
      𝟙 ((𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙ moduleUnboundedDerivedLowerShriek C.j Λ ⋙
        moduleUnboundedDerivedDirectImage Λ C.p) := by
  have h := congrArg (Functor.whiskerLeft (𝟭 (DerivedCategory (ModuleSheaf X Λ))))
    (moduleUnboundedDerivedCompactificationImageIdentity Λ C)
  exact h.trans (Functor.whiskerLeft_id' _)

end AlgebraicGeometry.Scheme.EtaleCohomology
