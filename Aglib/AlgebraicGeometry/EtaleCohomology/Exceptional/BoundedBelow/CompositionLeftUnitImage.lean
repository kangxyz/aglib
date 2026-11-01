/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionModelMaps
public import Aglib.CategoryTheory.Functor.ImageUnitRestriction
public import Aglib.CategoryTheory.Functor.ImageUnitCompositionFormula
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters

/-! # The actual left-unit tower map contracts to its original mixed identity transition

The source is expanded by the original lower-shriek identity compositor. All
three ambient families remain independent. Turning this normalized supplied
triangle into the chosen exceptional unit law also requires the original
identity-factorization contraction and canonical model-family comparison.
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
  [firstModels : ∀ E : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification ((𝟙 X) ≫ f),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

/-- The literal original first-refinement unit, with its endpoint model fixed explicitly. -/
abbrev moduleLeftUnitFirstDelta :=
  @moduleDerivedProperRefinementComparison X
    (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
    (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X) _ _
    (Hom.CompactifiedComposition.leftUnit C).first.p (leftUnitTowerSourceSquare C)
    Λ _ hX (firstModels (Hom.CompactifiedComposition.leftUnit C).first) hX

/-- The original mixed-model identity unit on the total ambient. -/
abbrev moduleLeftUnitTotalDelta :=
  @moduleDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
    (𝟙 C.Xbar) (leftUnitTowerTotalSquare C) Λ _ hX
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C)

/-- The exact original central exchange of the left-unit tower. -/
abbrev moduleLeftUnitCentralMate :=
  @moduleProperOpenMate Λ _ X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
    C.Xbar C.Xbar C.j (leftUnitMiddleOpen C)
    (Hom.CompactifiedComposition.leftUnit C).first.p (𝟙 C.Xbar) _ _
    (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen.flip hX
    (firstModels (Hom.CompactifiedComposition.leftUnit C).first) (targetModels C)
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)

/-- The original image compositor, with the independent middle ambient retained. -/
abbrev moduleLeftUnitImageContraction :=
  (@moduleDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar) hY
    (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)).symm

omit hY targetModels in
/-- The inverse expansion is exactly the original supplied-tower open compositor. -/
theorem moduleLeftUnitSourceExpansion_symm :
    (moduleLeftUnitSourceExpansion C Λ hX
      (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)).symm =
    moduleCompactifiedCompositionOpenIso (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C) := by
  apply Iso.ext
  rfl

/-- The actual supplied-tower map, not a replacement map, has the original unit-image formula. -/
theorem moduleLeftUnitCompositionFormula :
    ImageUnitHorizontalFormula
      (J' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (L := @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (L' := @moduleDerivedLowerShriek (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        C.Xbar (leftUnitMiddleOpen C) _ Λ _
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (R := @moduleDerivedDirectImage X Λ _
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (S := @moduleDerivedDirectImage C.Xbar Λ _ C.Xbar (𝟙 C.Xbar)
        (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (P := @moduleDerivedDirectImage Y Λ _ C.Xbar C.p hY (targetModels C))
      (P' := @moduleDerivedDirectImage Y Λ _ C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (moduleLeftUnitCentralMate f Λ C)
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleLeftUnitSourceExpansion C Λ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)))
      (moduleLeftUnitImageContraction f Λ C)
      (moduleCompactifiedCompositionAmbientIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C)).hom := by
  refine imageUnitHorizontalFormula_of_composition
      (J' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (L := @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (L' := @moduleDerivedLowerShriek (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        C.Xbar (leftUnitMiddleOpen C) _ Λ _
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (R := @moduleDerivedDirectImage X Λ _
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (S := @moduleDerivedDirectImage C.Xbar Λ _ C.Xbar (𝟙 C.Xbar)
        (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (P := @moduleDerivedDirectImage Y Λ _ C.Xbar C.p hY (targetModels C))
      (P' := @moduleDerivedDirectImage Y Λ _ C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
    (moduleLeftUnitCentralMate f Λ C)
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleCompactifiedCompositionOpenIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C)))
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleLeftUnitSourceExpansion C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)))
    (moduleLeftUnitImageContraction f Λ C)
    (moduleCompactifiedCompositionAmbientIso (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C)).hom ?_ ?_
  · exact (congrArg (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι)
      (moduleLeftUnitSourceExpansion_symm f Λ C)).symm
  · exact moduleCompactifiedCompositionAmbientIso_formula (𝟙 X) f Λ
      (C := Hom.CompactifiedComposition.leftUnit C)


/-- The actual normalized left-unit tower triangle is its original mixed identity transition. -/
theorem moduleLeftUnitCompositionImageEquation :
    ImageUnitHorizontalEquation
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (J' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (T' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (L := @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (R := @moduleDerivedDirectImage X Λ _
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (S := @moduleDerivedDirectImage C.Xbar Λ _ C.Xbar (𝟙 C.Xbar)
        (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (P := @moduleDerivedDirectImage Y Λ _ C.Xbar C.p hY (targetModels C))
      (P' := @moduleDerivedDirectImage Y Λ _ C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleLeftUnitFirstDelta f Λ C))
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleLeftUnitTotalDelta f Λ C))
      (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleLeftUnitTargetExpansion C Λ hX (targetModels C)))
      (moduleLeftUnitImageContraction f Λ C)
      (moduleCompactifiedCompositionAmbientIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C)).hom :=
  imageUnitHorizontalEquation _ _ (moduleLeftUnitCentralMate f Λ C) _
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleLeftUnitSourceExpansion C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))) _ _
    (unitMateHorizontalEquation_whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      _ _ _ _ _ (moduleLeftUnitTowerTotalOpenEquation C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C)))
    (moduleLeftUnitCompositionFormula f Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
