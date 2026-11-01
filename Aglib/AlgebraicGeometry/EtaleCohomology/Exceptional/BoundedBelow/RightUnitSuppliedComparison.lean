/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RightUnitSupplied
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RightUnitTotalComparison
public import Aglib.CategoryTheory.Functor.ImageRightUnitComparison

/-! # The original supplied right-unit triangle along the actual dense refinement -/

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

/-- The actual original first-to-total refinement map, with its independent two models. -/
abbrev moduleRightUnitSuppliedRefinement :=
  @moduleCompactificationMixedTransition X Y f _ Λ _ hX hY
    (Hom.CompactifiedComposition.rightUnit C).first
    (Hom.DenseCompactification.ofArrowEq (Category.comp_id f)
      (Hom.CompactifiedComposition.rightUnit C).composite)
    (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C)
    (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)

/-- The original identity-factorization contraction on the actual first proper image. -/
abbrev moduleRightUnitSuppliedContraction :=
  Functor.isoWhiskerLeft
    (((moduleTorsionCohomologyPlus X Λ).ι ⋙
      @moduleDerivedLowerShriek X (rightUnitFirstAmbient C) (rightUnitFirstOpen C) _ Λ _ hX
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)) ⋙
      @moduleDerivedDirectImage Y Λ _ (rightUnitFirstAmbient C)
        (Hom.CompactifiedComposition.rightUnit C).first.p hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first))
    (moduleDerivedIdentityFactorizationIso Λ Y hY
      (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification)) ≪≫
    Functor.rightUnitor _

/-- The supplied right-unit compositor followed by the literal first-to-total mixed transition
is the original identity-factorization contraction, retaining all middle models. -/
theorem moduleRightUnitSuppliedMixedEquation :
    (moduleCompactifiedCompositionAmbientIso
      (firstModels := firstModels) (secondModels := targetModels)
      (compositeModels := compositeModels) f (𝟙 Y) Λ
      (Hom.CompactifiedComposition.rightUnit C)).hom ≫ moduleRightUnitSuppliedRefinement
        (firstModels := firstModels) (compositeModels := compositeModels) f Λ C =
      (moduleRightUnitSuppliedContraction
        (firstModels := firstModels) (targetModels := targetModels) f Λ C).hom :=
  rightUnitImageEquation_actualComparison_hom
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
      (Hom.CompactifiedComposition.rightUnit C)).hom
      (moduleRightUnitSuppliedRefinement
        (firstModels := firstModels) (compositeModels := compositeModels) f Λ C)
      (moduleRightUnitTotalMixedTransition C Λ hX hY
        (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite))
      (moduleRightUnitSuppliedEquation
        (firstModels := firstModels) (targetModels := targetModels)
        (compositeModels := compositeModels) f Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
