/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitOpen
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageRefinement
public import Aglib.CategoryTheory.Adjunction.OuterComparisonEquation

/-! # The original central right-unit mate and original refinement-to-direct comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wY wA wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ))
  (hA : HasDerivedCategory.{wA} (ModuleSheaf (rightUnitFirstAmbient C) Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf Y Λ))

/-- The literal original structural image square of the right-unit tower. -/
abbrev moduleRightUnitStructuralSquare :=
  @moduleDerivedDirectImageSquareIso Λ _ C.Xbar (rightUnitFirstAmbient C) Y Y
    C.p (Hom.CompactifiedComposition.rightUnit C).first.p (𝟙 Y) (rightUnitMiddleOpen C)
    (Hom.CompactifiedComposition.rightUnit C).isPullback_middleOpen.flip.w hB hD hA hY

/-- The original refinement-based middle comparison is the canonical native triple map. -/
theorem moduleRightUnitMiddleOpenToDirect_eq :
    @moduleRightUnitMiddleOpenToDirect _ _ f C Λ _ hA hB =
      @moduleDerivedLowerShriekToDirectImage Λ _ (rightUnitFirstAmbient C) C.Xbar
        (rightUnitMiddleOpen C) _ hA hB :=
  @moduleDerivedProperRefinementComparison_toDirectImage Λ _
    (rightUnitFirstAmbient C) C.Xbar (rightUnitMiddleOpen C) _ hA hB
    (rightUnitOpenMiddleSquare C)

/-- The actual central mate is compatible with the original refinement-to-direct map.
The identity open still goes from `hY` to the independent model `hD`. -/
theorem moduleRightUnitMiddleOuterEquation :
    OuterComparisonEquation
      (moduleRightUnitCentralMate C Λ hY hA hB hD)
      (@moduleRightUnitMiddleOpenToDirect _ _ f C Λ _ hA hB)
      (@moduleDerivedLowerShriekToDirectImage Λ _ Y Y (𝟙 Y) _ hY hD)
      (moduleRightUnitStructuralSquare C Λ hY hA hB hD).hom :=
  outerComparisonEquation_of_triple
    (@moduleDerivedOpenTriple Λ _ Y Y (𝟙 Y) _ hY hD)
    (@moduleDerivedOpenTriple Λ _ (rightUnitFirstAmbient C) C.Xbar
      (rightUnitMiddleOpen C) _ hA hB)
    (moduleRightUnitCentralMate C Λ hY hA hB hD)
    (@moduleRightUnitMiddleOpenToDirect _ _ f C Λ _ hA hB)
    (@moduleDerivedLowerShriekToDirectImage Λ _ Y Y (𝟙 Y) _ hY hD)
    (moduleRightUnitStructuralSquare C Λ hY hA hB hD).hom
    (moduleRightUnitMiddleOpenToDirect_eq C Λ hA hB) rfl
    (@moduleProperOpenMate_toDirectImageSquare Λ _ Y (rightUnitFirstAmbient C) Y C.Xbar
      (𝟙 Y) (rightUnitMiddleOpen C) (Hom.CompactifiedComposition.rightUnit C).first.p
      C.p _ _ (Hom.CompactifiedComposition.rightUnit C).isPullback_middleOpen.flip
      hY hA hD hB)

end AlgebraicGeometry.Scheme.EtaleCohomology
