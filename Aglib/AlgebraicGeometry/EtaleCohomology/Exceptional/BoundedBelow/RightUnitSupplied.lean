/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitFace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitMiddle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitImage

/-! # The actual supplied right-unit triangle with its original raw refinement comparison -/

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

/-- The unchanged supplied compositor followed by the original raw refinement image comparison
is precisely the original identity-factorization contraction on its proper image. -/
theorem moduleRightUnitSuppliedEquation :
    RightUnitImageEquation
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X
          (Hom.CompactifiedComposition.rightUnit C).first.Xbar
          (Hom.CompactifiedComposition.rightUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (L := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (Q := @moduleDerivedDirectImage Y Λ _
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.p hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (I := @moduleDerivedLowerShriek Y Y (𝟙 Y) _ Λ _ hY
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (R := @moduleDerivedDirectImage Y Λ _ Y (𝟙 Y) hY
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (P₀ := @moduleDerivedDirectImage Y Λ _ C.Xbar (C.p ≫ 𝟙 Y) hY
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (N := @moduleDerivedDirectImage C.Xbar Λ _
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar (rightUnitMiddleOpen C)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleRightUnitSourceDelta
        (firstModels := firstModels) (compositeModels := compositeModels) f Λ C))
      (moduleRightUnitMiddleOverIso C Λ hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (moduleDerivedIdentityFactorizationIso Λ Y hY
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (moduleCompactifiedCompositionAmbientIso
        (firstModels := firstModels) (secondModels := targetModels)
        (compositeModels := compositeModels) f (𝟙 Y) Λ
        (Hom.CompactifiedComposition.rightUnit C)).hom :=
  rightUnitImageEquation
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X
          (Hom.CompactifiedComposition.rightUnit C).first.Xbar
          (Hom.CompactifiedComposition.rightUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (L := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (M := @moduleDerivedLowerShriek
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
      (P := @moduleDerivedDirectImage Y Λ _ C.Xbar C.p
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (R := @moduleDerivedDirectImage Y Λ _ Y (𝟙 Y) hY
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (P₀ := @moduleDerivedDirectImage Y Λ _ C.Xbar (C.p ≫ 𝟙 Y) hY
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (N := @moduleDerivedDirectImage C.Xbar Λ _
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar (rightUnitMiddleOpen C)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
      (moduleRightUnitCentralMate C Λ hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleCompactifiedCompositionOpenIso (firstModels := firstModels)
          (compositeModels := compositeModels) f (𝟙 Y) Λ
          (Hom.CompactifiedComposition.rightUnit C)))
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleRightUnitSourceDelta
        (firstModels := firstModels) (compositeModels := compositeModels) f Λ C))
      (@moduleRightUnitMiddleOpenToDirect _ _ f C Λ _
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (moduleRightUnitImageContraction
        (targetModels := targetModels) (compositeModels := compositeModels) f Λ C)
      (moduleRightUnitMiddleOverIso C Λ hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (moduleDerivedIdentityFactorizationIso Λ Y hY
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (moduleCompactifiedCompositionAmbientIso
        (firstModels := firstModels) (secondModels := targetModels)
        (compositeModels := compositeModels) f (𝟙 Y) Λ
        (Hom.CompactifiedComposition.rightUnit C)).hom
      (moduleRightUnitSourceEquation
        (firstModels := firstModels) (compositeModels := compositeModels) f Λ C)
      (moduleRightUnitMiddleEquation C Λ hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)
        (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification))
      (moduleRightUnitCompositionFormula
        (firstModels := firstModels) (targetModels := targetModels)
        (compositeModels := compositeModels) f Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
