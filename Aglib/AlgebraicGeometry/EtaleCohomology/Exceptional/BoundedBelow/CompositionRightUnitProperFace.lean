/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitMiddleComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitStructural

/-! # The literal original proper-image face of the supplied right-unit tower -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wY wA wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : Hom.DenseCompactification f)

/-- The original middle refinement retains the composite proper side `p ≫ id`. -/
theorem rightUnitMiddleProperFactorization :
    rightUnitMiddleOpen C ≫ (C.p ≫ 𝟙 Y) =
      (Hom.CompactifiedComposition.rightUnit C).first.p := by
  rw [Category.comp_id]
  exact (Hom.CompactifiedComposition.rightUnitFirstRefinement C).base_fac

variable (Λ : Type (u + 1)) [Ring Λ]
  (hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ))
  (hA : HasDerivedCategory.{wA} (ModuleSheaf (rightUnitFirstAmbient C) Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf Y Λ))

/-- The actual proper compositor through the independent identity middle model. -/
abbrev moduleRightUnitProperFaceContraction :=
  (@moduleDerivedDirectImageCompIso Λ _ Y Y C.Xbar (𝟙 Y) C.p hY hD hB).symm

/-- The original over-base comparison with the unchanged composite proper map. -/
abbrev moduleRightUnitMiddleOverIso :=
  @moduleDerivedDirectImageOverIso Λ _ Y (rightUnitFirstAmbient C) C.Xbar hY hA hB
    (Hom.CompactifiedComposition.rightUnit C).first.p (C.p ≫ 𝟙 Y) (rightUnitMiddleOpen C)
    (rightUnitMiddleProperFactorization C)

/-- The original identity-image contraction, retaining both independent models on `Y`. -/
abbrev moduleRightUnitIdentityImageContraction :=
  @moduleDerivedDirectImageOverIso Λ _ Y Y Y hY hY hD
    (𝟙 Y) (𝟙 Y) (𝟙 Y) (Category.comp_id (𝟙 Y)) ≪≫
    @moduleDerivedDirectImageIdIso Λ _ Y hY

/-- The actual proper-image structural face follows from the original retraction triangles. -/
theorem moduleRightUnitProperFaceEquation :
    RightUnitStructuralEquation
      (moduleRightUnitStructuralSquare C Λ hY hA hB hD)
      (moduleRightUnitProperFaceContraction C Λ hY hB hD)
      (moduleRightUnitMiddleOverIso C Λ hY hA hB)
      (moduleRightUnitIdentityImageContraction Λ hY hD) :=
  @moduleDerivedDirectImageSquareIso_retraction Λ _
    (rightUnitFirstAmbient C) C.Xbar Y Y
    (rightUnitMiddleOpen C) C.p (Hom.CompactifiedComposition.rightUnit C).first.p
    (𝟙 Y) (𝟙 Y) (Hom.CompactifiedComposition.rightUnit C).isPullback_middleOpen.flip.w
    (Category.comp_id (𝟙 Y)) (rightUnitMiddleProperFactorization C) hA hB hY hD

end AlgebraicGeometry.Scheme.EtaleCohomology
