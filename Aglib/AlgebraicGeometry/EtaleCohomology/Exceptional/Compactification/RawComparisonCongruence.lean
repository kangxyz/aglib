/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawIdentityComparison

/-! # Equality of the actual ambient refinement arrow preserves the original image map -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wC wD wS
variable {X C D S : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- This changes only the presentation of the actual refinement morphism. -/
theorem moduleRawImageComparison_congr
    (jC : X ⟶ C) (jD : X ⟶ D) [IsOpenImmersion jC] [IsOpenImmersion jD]
    (pC : C ⟶ S) (pD : D ⟶ S) (a b : C ⟶ D) (e : a = b)
    (sa : IsPullback jC (𝟙 X) a jD) (sb : IsPullback jC (𝟙 X) b jD)
    (ha : a ≫ pD = pC) (hb : b ≫ pD = pC) :
    CategoryTheory.imageComparison (moduleDerivedProperRefinementComparison jC jD a sa Λ)
        (moduleDerivedDirectImageOverIso Λ pC pD a ha) =
      CategoryTheory.imageComparison (moduleDerivedProperRefinementComparison jC jD b sb Λ)
        (moduleDerivedDirectImageOverIso Λ pC pD b hb) := by
  subst b
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
