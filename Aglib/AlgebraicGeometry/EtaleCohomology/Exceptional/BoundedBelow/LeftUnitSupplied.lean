/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitImage
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.LeftUnitSourceRestriction
public import Aglib.CategoryTheory.Functor.ImageLeftUnitEquation

/-! # The original source-contracted left-unit supplied-tower triangle -/

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

/-- The actual supplied composition and actual first transition contract to the total transition.
The identity model here is the endpoint model; other ambient models remain independent. -/
theorem moduleLeftUnitSuppliedEquation :
    ImageLeftUnitEquation
      (V := (moduleTorsionCohomologyPlus X Λ).ι)
      (I := @moduleDerivedDirectImage X Λ _ X (𝟙 X) hX hX)
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (J' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
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
        (moduleLeftUnitTotalDelta f Λ C))
      (moduleLeftUnitImageContraction f Λ C)
      (moduleCompactifiedCompositionAmbientIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C)).hom
      (moduleLeftUnitRestrictedContraction Λ hX)
      (moduleLeftUnitRestrictedFirstComparison C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)) := by
  exact imageLeftUnitEquation
      (V := (moduleTorsionCohomologyPlus X Λ).ι)
      (I := @moduleDerivedDirectImage X Λ _ X (𝟙 X) hX hX)
      (J := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (J' := (moduleTorsionCohomologyPlus X Λ).ι ⋙
        @moduleDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
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
        (Hom.CompactifiedComposition.leftUnit C)).hom
      (moduleLeftUnitRestrictedContraction Λ hX)
      (moduleLeftUnitRestrictedImageIdentity Λ hX)
      (moduleLeftUnitRestrictedFirstComparison C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (moduleLeftUnitRestrictedExpansion C Λ hX (targetModels C))
      (moduleLeftUnitRestrictedFirstComparison_eq C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (moduleLeftUnitCompositionImageEquation f Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
