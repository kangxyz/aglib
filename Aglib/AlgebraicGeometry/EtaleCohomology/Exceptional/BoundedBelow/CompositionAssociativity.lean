/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleSingleModelAssociativity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleChosenTotalComparison
public import Aglib.CategoryTheory.Functor.CompositionAssociativityTransfer

/-! # Associativity of the original chosen exceptional compositor

A genuine compactification triple supplies the original Cartesian model maps.
Their proved associativity descends through the original single-model comparison
squares. All seven compactification-model families remain independent.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wW wF wG wH wFG wGH wL wR
variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace W] [QuasiSeparatedSpace W]
  [IsSeparated f] [LocallyOfFiniteType f]
  [IsSeparated g] [LocallyOfFiniteType g]
  [IsSeparated h] [LocallyOfFiniteType h]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  [fModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [gModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [hModels : ∀ C : Hom.DenseCompactification h,
    HasDerivedCategory.{wH} (ModuleSheaf C.Xbar Λ)]
  [fgModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  [ghModels : ∀ C : Hom.DenseCompactification (g ≫ h),
    HasDerivedCategory.{wGH} (ModuleSheaf C.Xbar Λ)]
  [leftModels : ∀ C : Hom.DenseCompactification ((f ≫ g) ≫ h),
    HasDerivedCategory.{wL} (ModuleSheaf C.Xbar Λ)]
  [rightModels : ∀ C : Hom.DenseCompactification (f ≫ (g ≫ h)),
    HasDerivedCategory.{wR} (ModuleSheaf C.Xbar Λ)]

/-- The original chosen compositor is associative, with only the original
scheme-arrow congruence identifying the two total targets. -/
theorem moduleExceptionalCompositionIso_assoc :
    Functor.isoWhiskerRight
        (moduleExceptionalCompositionIso (firstModels := fModels)
          (secondModels := gModels) (compositeModels := fgModels) f g Λ)
        (moduleExceptionalDirectImagePlusTorsion h Λ) ≪≫
      moduleExceptionalCompositionIso (firstModels := fgModels)
        (secondModels := hModels) (compositeModels := leftModels) (f ≫ g) h Λ ≪≫
      moduleExceptionalDirectImagePlusTorsionCongr Λ hX hW (Category.assoc f g h)
        leftModels rightModels =
    Functor.associator
        (moduleExceptionalDirectImagePlusTorsion f Λ)
        (moduleExceptionalDirectImagePlusTorsion g Λ)
        (moduleExceptionalDirectImagePlusTorsion h Λ) ≪≫
      Functor.isoWhiskerLeft
        (moduleExceptionalDirectImagePlusTorsion f Λ)
        (moduleExceptionalCompositionIso (firstModels := gModels)
          (secondModels := hModels) (compositeModels := ghModels) g h Λ) ≪≫
      moduleExceptionalCompositionIso (firstModels := fModels)
        (secondModels := ghModels) (compositeModels := rightModels) f (g ≫ h) Λ := by
  let T : Hom.TripleCompactifiedComposition f g h := Classical.choice inferInstance
  let hA₀ := fModels T.leftInner.first
  let hB₀ := gModels T.tail.first
  let hA₁ := fgModels T.leftInner.composite
  let hA₂ := leftModels T.leftOuter.composite
  apply compositionAssociativity_transfer
    (moduleExceptionalSingleTorsionValueIso (models := fModels) f Λ T.leftInner.first hA₀)
    (moduleExceptionalSingleTorsionValueIso (models := gModels) g Λ T.tail.first hB₀)
    (moduleExceptionalSingleTorsionValueIso (models := hModels) h Λ T.last (hModels T.last))
    (moduleExceptionalSingleTorsionValueIso (models := fgModels)
      (f ≫ g) Λ T.leftInner.composite hA₁)
    (moduleExceptionalSingleTorsionValueIso (models := ghModels)
      (g ≫ h) Λ T.tail.composite (ghModels T.tail.composite))
    (moduleExceptionalSingleTorsionValueIso (models := leftModels)
      ((f ≫ g) ≫ h) Λ T.leftOuter.composite hA₂)
    (moduleExceptionalSingleTorsionValueIso (models := rightModels)
      (f ≫ (g ≫ h)) Λ T.rightOuter.composite hA₂)
    _ _ _ _ _
    (moduleExceptionalCompositionSingleModelIso (firstModels := fModels)
      (secondModels := gModels) (compositeModels := fgModels)
      f g Λ T.leftInner T.leftInner.first hA₀ hA₁)
    (moduleExceptionalCompositionSingleModelIso (firstModels := fgModels)
      (secondModels := hModels) (compositeModels := leftModels)
      (f ≫ g) h Λ T.leftOuter T.leftInner.composite hA₁ hA₂)
    (moduleExceptionalCompositionSingleModelIso (firstModels := gModels)
      (secondModels := hModels) (compositeModels := ghModels)
      g h Λ T.tail T.tail.first hB₀ (ghModels T.tail.composite))
    (moduleExceptionalCompositionSingleModelIso (firstModels := fModels)
      (secondModels := ghModels) (compositeModels := rightModels)
      f (g ≫ h) Λ T.rightOuter T.leftInner.first hA₀ hA₂)
    (moduleCompactificationSingleTorsionTransition Λ T.totalArrowRefinement hA₂ hA₂).symm
  · exact moduleExceptionalCompositionSingleModelIso_comparison f g Λ
      T.leftInner T.leftInner.first hA₀ hA₁
  · exact moduleExceptionalCompositionSingleModelIso_comparison (f ≫ g) h Λ
      T.leftOuter T.leftInner.composite hA₁ hA₂
  · exact moduleExceptionalCompositionSingleModelIso_comparison g h Λ
      T.tail T.tail.first hB₀ (ghModels T.tail.composite)
  · exact moduleExceptionalCompositionSingleModelIso_comparison f (g ≫ h) Λ
      T.rightOuter T.leftInner.first hA₀ hA₂
  · exact moduleTripleChosenTotalComparison T Λ leftModels rightModels hA₂
  · exact moduleTripleSingleModelAssociativity T Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
