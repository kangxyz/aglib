/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.FaithfulComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleSingleModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionSingleModelUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleCartesianComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleTotalArrowComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsionMap
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionComparisonSquares

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
local instance tripleSingleAssocA0 :
    HasDerivedCategory.{wF} (ModuleSheaf T.leftInner.first.Xbar Λ) :=
  fModels T.leftInner.first
/-- The local derived-category model on `ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ`.
-/
local instance tripleSingleAssocA1 :
    HasDerivedCategory.{wFG} (ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ) :=
  fgModels T.leftInner.composite
/-- The local derived-category model on `ModuleSheaf T.first.Xbar Λ`. -/
local instance tripleSingleAssocA2 :
    HasDerivedCategory.{wL} (ModuleSheaf T.first.Xbar Λ) :=
  leftModels T.leftOuter.composite
/-- The local derived-category model on `ModuleSheaf T.tail.first.Xbar Λ`. -/
local instance tripleSingleAssocB0 :
    HasDerivedCategory.{wG} (ModuleSheaf T.tail.first.Xbar Λ) := gModels T.tail.first
/-- The local derived-category model on `ModuleSheaf T.middle.Xbar Λ`. -/
local instance tripleSingleAssocB1 :
    HasDerivedCategory.{wGH} (ModuleSheaf T.middle.Xbar Λ) := ghModels T.tail.composite
/-- The local derived-category model on `ModuleSheaf T.last.Xbar Λ`. -/
local instance tripleSingleAssocC :
    HasDerivedCategory.{wH} (ModuleSheaf T.last.Xbar Λ) := hModels T.last
local instance tripleSingleAssocLeftOpen : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion
local instance tripleSingleAssocRightOpen : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

private theorem identityMiddleSquare {A B : Scheme.{u}} (m : A ⟶ B) :
    IsPullback m (𝟙 A) (𝟙 B) m :=
  IsPullback.of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

/-- Forgetting the native torsion property gives the proved original four-map equation. -/
theorem moduleTripleSingleModelFaithfulComposition :
    FaithfulCompositionEquation (moduleTorsionCohomologyPlus W Λ).ι
      (moduleTripleSingleInnerIso T Λ) (moduleTripleSingleLeftIso T Λ)
      (moduleTripleSingleRightIso T Λ) (moduleTripleSingleTailIso T Λ)
      (moduleTripleSingleTotalIso T Λ) := by
  intro K
  have hInner := moduleExceptionalCompositionSingleModelIso_underlying_hom_app f g Λ
    (firstModels := fModels) (secondModels := gModels) (compositeModels := fgModels)
    T.leftInner T.leftInner.first (fModels T.leftInner.first) (fgModels T.leftInner.composite)
    T.leftInner.middleOpen T.leftInner.isPullback_middleOpen (𝟙 T.leftInner.first)
    (identityMiddleSquare T.leftInner.middleOpen) T.leftInner.first_j_middleOpen K
  have hInnerMapped :=
    (moduleCompactificationSingleTorsionValue_map_hom Λ T.last (hModels T.last)
      ((moduleTripleSingleInnerIso T Λ).hom.app K)).trans
    (congrArg (fun t => (moduleDerivedDirectImage Λ T.last.p).map
      ((moduleDerivedLowerShriek T.last.j Λ).map t)) hInner)
  have hLeft := moduleExceptionalCompositionSingleModelIso_underlying_hom_app (f ≫ g) h Λ
    (firstModels := fgModels) (secondModels := hModels) (compositeModels := leftModels)
    T.leftOuter T.leftInner.composite
    (fgModels T.leftInner.composite) (leftModels T.leftOuter.composite)
    T.innerToFirst T.isPullback_leftInner T.leftIntermediateRefinement
    T.isPullback_leftIntermediateComparison.flip T.leftInner_j_innerToFirst K
  have hTail := moduleExceptionalCompositionSingleModelIso_underlying_hom_app g h Λ
    (firstModels := gModels) (secondModels := hModels) (compositeModels := ghModels)
    T.tail T.tail.first (gModels T.tail.first) (ghModels T.tail.composite)
    T.tail.middleOpen T.tail.isPullback_middleOpen (𝟙 T.tail.first)
    (identityMiddleSquare T.tail.middleOpen) T.tail.first_j_middleOpen
    ((moduleTripleSingleFirstValue T Λ).obj K)
  have hRight := moduleExceptionalCompositionSingleModelIso_underlying_hom_app f (g ≫ h) Λ
    (firstModels := fModels) (secondModels := ghModels) (compositeModels := rightModels)
    T.rightOuter T.leftInner.first
    (fModels T.leftInner.first) (leftModels T.leftOuter.composite)
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.isPullback_first T.firstRefinement
    T.isPullback_firstComparison.flip (tripleFirstOpenEquality T) K
  have hTotal :=
    (moduleCompactificationSingleTorsionTransition_hom_app Λ T.totalArrowRefinement
      (leftModels T.leftOuter.composite) (leftModels T.leftOuter.composite) K).trans
    (congrArg (fun t => t.app K) (moduleTripleTotalArrowMixedComparison T Λ))
  have hRaw := congrArg (fun t => t.app K.obj) (moduleTripleCartesianComposition T Λ)
  exact compositionEquation_of_formulas _ _ _ _ _ _ _ _ _ _
    hInnerMapped hLeft hTail hRight hTotal hRaw

/-- The genuine supplied triple has the original native map associativity, with all seven
families independent and the original total-arrow comparison inverted only at the end. -/
theorem moduleTripleSingleModelAssociativity :
    OpenCompositionEquation
      (moduleTripleSingleInnerIso T Λ)
      (moduleTripleSingleLeftIso T Λ ≪≫ (moduleTripleSingleTotalIso T Λ).symm)
      (moduleTripleSingleRightIso T Λ) (moduleTripleSingleTailIso T Λ) :=
  openCompositionEquation_of_post _ _ _ _ _
    (openCompositionPostEquation_of_faithful (moduleTorsionCohomologyPlus W Λ).ι
      _ _ _ _ _ (moduleTripleSingleModelFaithfulComposition T Λ))

end AlgebraicGeometry.Scheme.EtaleCohomology
