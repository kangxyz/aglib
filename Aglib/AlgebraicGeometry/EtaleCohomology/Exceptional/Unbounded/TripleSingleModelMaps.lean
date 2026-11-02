/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleSingleModels
public import
Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionSingleModelFormulaBoundary
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleCartesianComposition
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleTotalArrowComparison
public import
  Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionComparisonSquares

/-! # Original single-value models of the genuine triple tower -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wW wF wG wH wFG wGH wL wR
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  [IsSeparated f] [IsSeparated g] [IsSeparated h]
  [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace W] [QuasiSeparatedSpace W]
  (T : Hom.TripleCompactifiedComposition f g h) (Λ : Type (u + 1)) [Ring Λ]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  [fModels : ∀ C : Hom.DenseCompactification f, HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [gModels : ∀ C : Hom.DenseCompactification g, HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [hModels : ∀ C : Hom.DenseCompactification h, HasDerivedCategory.{wH} (ModuleSheaf C.Xbar Λ)]
  [fgModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  [ghModels : ∀ C : Hom.DenseCompactification (g ≫ h),
    HasDerivedCategory.{wGH} (ModuleSheaf C.Xbar Λ)]
  [leftModels : ∀ C : Hom.DenseCompactification ((f ≫ g) ≫ h),
    HasDerivedCategory.{wL} (ModuleSheaf C.Xbar Λ)]
  [rightModels : ∀ C : Hom.DenseCompactification (f ≫ (g ≫ h)),
    HasDerivedCategory.{wR} (ModuleSheaf C.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf T.leftInner.first.Xbar Λ`. -/
local instance unboundedTripleSingleAssocA0 :
    HasDerivedCategory.{wF} (ModuleSheaf T.leftInner.first.Xbar Λ) :=
  fModels T.leftInner.first
/-- The local derived-category model on `ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ`.
-/
local instance unboundedTripleSingleAssocA1 :
    HasDerivedCategory.{wFG} (ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ) :=
  fgModels T.leftInner.composite
/-- The local derived-category model on `ModuleSheaf T.first.Xbar Λ`. -/
local instance unboundedTripleSingleAssocA2 :
    HasDerivedCategory.{wL} (ModuleSheaf T.first.Xbar Λ) :=
  leftModels T.leftOuter.composite
/-- The local derived-category model on `ModuleSheaf T.tail.first.Xbar Λ`. -/
local instance unboundedTripleSingleAssocB0 :
    HasDerivedCategory.{wG} (ModuleSheaf T.tail.first.Xbar Λ) := gModels T.tail.first
/-- The local derived-category model on `ModuleSheaf T.middle.Xbar Λ`. -/
local instance unboundedTripleSingleAssocB1 :
    HasDerivedCategory.{wGH} (ModuleSheaf T.middle.Xbar Λ) := ghModels T.tail.composite
/-- The local derived-category model on `ModuleSheaf T.last.Xbar Λ`. -/
local instance unboundedTripleSingleAssocC :
    HasDerivedCategory.{wH} (ModuleSheaf T.last.Xbar Λ) := hModels T.last
local instance unboundedTripleSingleAssocLeftOpen : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion
local instance unboundedTripleSingleAssocRightOpen : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

private theorem identityMiddleSquare {A B : Scheme.{u}} (m : A ⟶ B) :
    IsPullback m (𝟙 A) (𝟙 B) m :=
  IsPullback.of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

omit [IsSeparated h] [LocallyOfFiniteType h] [CompactSpace W] [QuasiSeparatedSpace W]
  hW hModels ghModels leftModels rightModels in
/-- The original inner single-value compositor has the proved whole Cartesian map. -/
theorem moduleUnboundedTripleSingleInnerIso_formula :
    OriginalIsoHomFormula (moduleUnboundedTripleSingleInnerIso T Λ N hN hΛ)
      (moduleUnboundedTripleLeftInnerMap T Λ) := by
  exact moduleExceptionalUnboundedCompositionSingleModelIso_formula f g Λ N hN hΛ
    (firstModels := fModels) (secondModels := gModels) (compositeModels := fgModels)
    T.leftInner T.leftInner.first (fModels T.leftInner.first) (fgModels T.leftInner.composite)
    T.leftInner.middleOpen T.leftInner.isPullback_middleOpen (𝟙 T.leftInner.first)
    (identityMiddleSquare T.leftInner.middleOpen) T.leftInner.first_j_middleOpen
    (moduleUnboundedTripleSingleInnerIso T Λ N hN hΛ)
    (moduleUnboundedTripleLeftInnerMap T Λ) rfl rfl

omit [CompactSpace Y] [QuasiSeparatedSpace Y] hY fModels gModels ghModels rightModels in
/-- The original left single-value compositor uses the actual intermediate restriction. -/
theorem moduleUnboundedTripleSingleLeftIso_formula :
    OriginalIsoHomFormula (moduleUnboundedTripleSingleLeftIso T Λ N hN hΛ)
      (moduleUnboundedTripleLeftOuterMap T Λ) := by
  exact moduleExceptionalUnboundedCompositionSingleModelIso_formula (f ≫ g) h Λ N hN hΛ
    (firstModels := fgModels) (secondModels := hModels) (compositeModels := leftModels)
    T.leftOuter T.leftInner.composite
    (fgModels T.leftInner.composite) (leftModels T.leftOuter.composite)
    T.innerToFirst T.isPullback_leftInner T.leftIntermediateRefinement
    T.isPullback_leftIntermediateComparison.flip T.leftInner_j_innerToFirst
    (moduleUnboundedTripleSingleLeftIso T Λ N hN hΛ)
    (moduleUnboundedTripleLeftOuterMap T Λ) rfl rfl

omit [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
  [CompactSpace Y] [QuasiSeparatedSpace Y] hX fModels fgModels leftModels rightModels in
/-- The original tail single-value compositor has the proved whole Cartesian map. -/
theorem moduleUnboundedTripleSingleTailIso_formula :
    OriginalIsoHomFormula (moduleUnboundedTripleSingleTailIso T Λ N hN hΛ)
      (moduleUnboundedTripleTailMap T Λ) := by
  exact moduleExceptionalUnboundedCompositionSingleModelIso_formula g h Λ N hN hΛ
    (firstModels := gModels) (secondModels := hModels) (compositeModels := ghModels)
    T.tail T.tail.first (gModels T.tail.first) (ghModels T.tail.composite)
    T.tail.middleOpen T.tail.isPullback_middleOpen (𝟙 T.tail.first)
    (identityMiddleSquare T.tail.middleOpen) T.tail.first_j_middleOpen
    (moduleUnboundedTripleSingleTailIso T Λ N hN hΛ)
    (moduleUnboundedTripleTailMap T Λ) rfl rfl

omit [CompactSpace Z] [QuasiSeparatedSpace Z] hZ gModels hModels fgModels in
/-- The original right compositor retains the independent right family and supplied top model. -/
theorem moduleUnboundedTripleSingleRightIso_formula :
    OriginalIsoHomFormula (moduleUnboundedTripleSingleRightIso T Λ N hN hΛ)
      (moduleUnboundedTripleRightOuterMap T Λ) := by
  exact moduleExceptionalUnboundedCompositionSingleModelIso_formula f (g ≫ h) Λ N hN hΛ
    (firstModels := fModels) (secondModels := ghModels) (compositeModels := rightModels)
    T.rightOuter T.leftInner.first
    (fModels T.leftInner.first) (leftModels T.leftOuter.composite)
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.isPullback_first T.firstRefinement
    T.isPullback_firstComparison.flip (unboundedTripleFirstOpenEquality T)
    (moduleUnboundedTripleSingleRightIso T Λ N hN hΛ)
    (moduleUnboundedTripleRightOuterMap T Λ) rfl rfl

omit [IsSeparated f] [IsSeparated g] [IsSeparated h]
  [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace W] [QuasiSeparatedSpace W]
  hY hZ fModels gModels hModels fgModels ghModels rightModels in
/-- The original total refinement is exactly the original proper associativity transport. -/
theorem moduleUnboundedTripleSingleTotalIso_formula :
    OriginalIsoHomFormula (moduleUnboundedTripleSingleTotalIso T Λ N hN hΛ)
      (Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek T.first.j Λ)
        (eqToHom (congrArg (fun p : T.first.Xbar ⟶ W => moduleUnboundedDerivedDirectImage Λ p)
          (Category.assoc T.first.p T.middle.p T.last.p).symm))) :=
  originalIsoHomFormula_of_hom_eq _ _ (moduleUnboundedTripleTotalArrowMixedComparison T Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
