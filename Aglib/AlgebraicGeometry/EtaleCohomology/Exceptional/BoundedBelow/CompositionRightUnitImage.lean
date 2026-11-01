/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitFace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters
public import Aglib.CategoryTheory.Functor.ImageRightUnit

/-! # The original right-unit tower composition formula

This identifies the accepted supplied compositor, rather than constructing a
replacement map. The central identity-open contraction and source-refinement
face required by `rightUnitImageEquation` are separate obligations.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification (𝟙 Y),
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification (f ≫ 𝟙 Y),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

/-- The original proper compositor through the independent identity middle model. -/
abbrev moduleRightUnitImageContraction :=
  (@moduleDerivedDirectImageCompIso Λ _ Y Y C.Xbar (𝟙 Y) C.p hY
    (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification)
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)).symm

omit [QuasiCompact f] in
/-- The exact accepted right-unit tower map has its original mixed-mate formula. -/
theorem moduleRightUnitCompositionFormula :
    ImageCompositionFormula
      (K := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X
          (Hom.CompactifiedComposition.rightUnit C).first.Xbar
          (Hom.CompactifiedComposition.rightUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (L := @moduleDerivedLowerShriek
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar C.Xbar
        (rightUnitMiddleOpen C) _ Λ _
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (Q := @moduleDerivedDirectImage Y Λ _
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.p hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (I := @moduleDerivedLowerShriek Y Y (𝟙 Y) _ Λ _ hY
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (R := @moduleDerivedDirectImage Y Λ _ C.Xbar C.p
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (P := @moduleDerivedDirectImage Y Λ _ Y (𝟙 Y) hY
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (S := @moduleDerivedDirectImage Y Λ _ C.Xbar (C.p ≫ 𝟙 Y) hY
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (moduleRightUnitCentralMate C Λ hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleCompactifiedCompositionOpenIso (firstModels := firstModels)
          (compositeModels := compositeModels) f (𝟙 Y) Λ
          (Hom.CompactifiedComposition.rightUnit C)))
      (moduleRightUnitImageContraction f Λ C)
      (moduleCompactifiedCompositionAmbientIso
        (firstModels := firstModels) (secondModels := targetModels)
        (compositeModels := compositeModels) f (𝟙 Y) Λ
        (Hom.CompactifiedComposition.rightUnit C)).hom :=
  moduleCompactifiedCompositionAmbientIso_formula
    (firstModels := firstModels) (secondModels := targetModels)
    (compositeModels := compositeModels) f (𝟙 Y) Λ
    (C := Hom.CompactifiedComposition.rightUnit C)

end AlgebraicGeometry.Scheme.EtaleCohomology
