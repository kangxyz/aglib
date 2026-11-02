/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleSingleModelAssociativity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleChosenTotalComparison
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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original chosen compositor is associative, with only the original
scheme-arrow congruence identifying the two total targets. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_assoc :
    Functor.isoWhiskerRight
        (moduleExceptionalDirectImageUnboundedCompIso (firstModels := fModels)
          (secondModels := gModels) (compositeModels := fgModels) f g Λ N hN hΛ)
        ((@moduleExceptionalDirectImageUnbounded _ _ _ _ h _ _ _ Λ _ _ _ (hModels
          (moduleExceptionalCompactification h)))) ≪≫
      moduleExceptionalDirectImageUnboundedCompIso (firstModels := fgModels)
        (secondModels := hModels) (compositeModels := leftModels) (f ≫ g) h Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedCongr Λ hX hW (Category.assoc f g h)
        leftModels rightModels N hN hΛ =
    Functor.associator
        ((@moduleExceptionalDirectImageUnbounded _ _ _ _ f _ _ _ Λ _ _ _ (fModels
          (moduleExceptionalCompactification f))))
        ((@moduleExceptionalDirectImageUnbounded _ _ _ _ g _ _ _ Λ _ _ _ (gModels
          (moduleExceptionalCompactification g))))
        ((@moduleExceptionalDirectImageUnbounded _ _ _ _ h _ _ _ Λ _ _ _ (hModels
          (moduleExceptionalCompactification h)))) ≪≫
      Functor.isoWhiskerLeft
        ((@moduleExceptionalDirectImageUnbounded _ _ _ _ f _ _ _ Λ _ _ _ (fModels
          (moduleExceptionalCompactification f))))
        (moduleExceptionalDirectImageUnboundedCompIso (firstModels := gModels)
          (secondModels := hModels) (compositeModels := ghModels) g h Λ N hN hΛ) ≪≫
      moduleExceptionalDirectImageUnboundedCompIso (firstModels := fModels)
        (secondModels := ghModels) (compositeModels := rightModels) f (g ≫ h) Λ N hN hΛ := by
  let T : Hom.TripleCompactifiedComposition f g h := Classical.choice inferInstance
  let hA₀ := fModels T.leftInner.first
  let hB₀ := gModels T.tail.first
  let hA₁ := fgModels T.leftInner.composite
  let hA₂ := leftModels T.leftOuter.composite
  apply compositionAssociativity_transfer
    (moduleExceptionalUnboundedSingleValueIso (models := fModels) f Λ N hN hΛ T.leftInner.first hA₀)
    (moduleExceptionalUnboundedSingleValueIso (models := gModels) g Λ N hN hΛ T.tail.first hB₀)
    (moduleExceptionalUnboundedSingleValueIso (models := hModels) h Λ N hN hΛ T.last (hModels
      T.last))
    (moduleExceptionalUnboundedSingleValueIso (models := fgModels)
      (f ≫ g) Λ N hN hΛ T.leftInner.composite hA₁)
    (moduleExceptionalUnboundedSingleValueIso (models := ghModels)
      (g ≫ h) Λ N hN hΛ T.tail.composite (ghModels T.tail.composite))
    (moduleExceptionalUnboundedSingleValueIso (models := leftModels)
      ((f ≫ g) ≫ h) Λ N hN hΛ T.leftOuter.composite hA₂)
    (moduleExceptionalUnboundedSingleValueIso (models := rightModels)
      (f ≫ (g ≫ h)) Λ N hN hΛ T.rightOuter.composite hA₂)
    _ _ _ _ _
    (moduleExceptionalUnboundedCompositionSingleModelIso (firstModels := fModels)
      (secondModels := gModels) (compositeModels := fgModels)
      f g Λ N hN hΛ T.leftInner T.leftInner.first hA₀ hA₁)
    (moduleExceptionalUnboundedCompositionSingleModelIso (firstModels := fgModels)
      (secondModels := hModels) (compositeModels := leftModels)
      (f ≫ g) h Λ N hN hΛ T.leftOuter T.leftInner.composite hA₁ hA₂)
    (moduleExceptionalUnboundedCompositionSingleModelIso (firstModels := gModels)
      (secondModels := hModels) (compositeModels := ghModels)
      g h Λ N hN hΛ T.tail T.tail.first hB₀ (ghModels T.tail.composite))
    (moduleExceptionalUnboundedCompositionSingleModelIso (firstModels := fModels)
      (secondModels := ghModels) (compositeModels := rightModels)
      f (g ≫ h) Λ N hN hΛ T.rightOuter T.leftInner.first hA₀ hA₂)
    (moduleUnboundedCompactificationSingleTransitionIso Λ T.totalArrowRefinement hA₂ hA₂ N hN
      hΛ).symm
  · exact moduleExceptionalUnboundedCompositionSingleModelIso_comparison f g Λ N hN hΛ
      T.leftInner T.leftInner.first hA₀ hA₁
  · exact moduleExceptionalUnboundedCompositionSingleModelIso_comparison (f ≫ g) h Λ N hN hΛ
      T.leftOuter T.leftInner.composite hA₁ hA₂
  · exact moduleExceptionalUnboundedCompositionSingleModelIso_comparison g h Λ N hN hΛ
      T.tail T.tail.first hB₀ (ghModels T.tail.composite)
  · exact moduleExceptionalUnboundedCompositionSingleModelIso_comparison f (g ≫ h) Λ N hN hΛ
      T.rightOuter T.leftInner.first hA₀ hA₂
  · exact moduleUnboundedTripleChosenTotalComparison T Λ leftModels rightModels hA₂ N hN hΛ
  · exact moduleUnboundedTripleSingleModelAssociativity T Λ N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
