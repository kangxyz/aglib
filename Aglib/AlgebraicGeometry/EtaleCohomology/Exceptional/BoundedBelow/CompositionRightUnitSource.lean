/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionModelMaps
public import Aglib.CategoryTheory.Functor.ImageRightUnitRestriction

/-! # The actual supplied right-unit open compositor has its original source face -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification (f ≫ 𝟙 Y),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

omit [QuasiCompact f] in
/-- The normalized expansion is exactly the original supplied-tower open compositor. -/
theorem moduleRightUnitOpenExpansion_symm :
    (moduleRightUnitOpenExpansion
      (hX := hX) (hA := firstModels (Hom.CompactifiedComposition.rightUnit C).first)
      (hB := compositeModels (Hom.CompactifiedComposition.rightUnit C).composite) C Λ).symm =
    moduleCompactifiedCompositionOpenIso (firstModels := firstModels)
      (compositeModels := compositeModels) f (𝟙 Y) Λ
      (Hom.CompactifiedComposition.rightUnit C) := by
  apply Iso.ext
  rfl

/-- The exact original source refinement, retaining its source and final models. -/
abbrev moduleRightUnitSourceDelta :=
  @moduleDerivedProperRefinementComparison X (rightUnitFirstAmbient C) C.Xbar
    (rightUnitFirstOpen C) C.j _ _ (rightUnitMiddleOpen C) (rightUnitOpenTotalSquare C)
    Λ _ hX (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)

/-- The actual original supplied open compositor satisfies the restricted original source face. -/
theorem moduleRightUnitSourceEquation :
    RightUnitOpenEquation
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X (rightUnitFirstAmbient C) (rightUnitFirstOpen C) _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (L := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleCompactifiedCompositionOpenIso (firstModels := firstModels)
          (compositeModels := compositeModels) f (𝟙 Y) Λ
          (Hom.CompactifiedComposition.rightUnit C)))
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleRightUnitSourceDelta f Λ C))
      (@moduleRightUnitMiddleOpenToDirect X Y f C Λ _
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)) :=
  rightUnitOpenEquation_whiskerLeft_of_eq (moduleTorsionCohomologyPlus X Λ).ι _ _ _ _
    (moduleRightUnitOpenExpansion_symm f Λ C)
    (moduleRightUnitOpenEquation
      (hX := hX) (hA := firstModels (Hom.CompactifiedComposition.rightUnit C).first)
      (hB := compositeModels (Hom.CompactifiedComposition.rightUnit C).composite) C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
