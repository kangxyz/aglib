/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianFirstComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleOpenContraction
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionComparisonSquares

/-! # The actual outer alpha maps and the original triple pullback comparisons -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wW wF wFG wH wFGH wGH wR
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  (T : Hom.TripleCompactifiedComposition f g h) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]

local instance : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion

local instance : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

section Left
variable [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification h,
    HasDerivedCategory.{wH} (ModuleSheaf C.Xbar Λ)]
  [totalModels : ∀ C : Hom.DenseCompactification ((f ≫ g) ≫ h),
    HasDerivedCategory.{wFGH} (ModuleSheaf C.Xbar Λ)]
  [hInner : HasDerivedCategory.{wR} (ModuleSheaf T.leftInner.composite.Xbar Λ)]

/-- The left raw outer route is attached by the literal intermediate refinement map. -/
theorem moduleTripleLeftFirstComparison :
    Functor.whiskerRight
        (@moduleCompactificationMixedTransition X Z (f ≫ g) _ Λ _ hX hZ
          T.leftInner.composite T.leftOuter.first T.leftIntermediateRefinement
          hInner (firstModels T.leftOuter.first))
        (@moduleDerivedLowerShriek Z T.last.Xbar T.last.j _ Λ _ hZ (targetModels T.last) ⋙
          @moduleDerivedDirectImage W Λ _ T.last.Xbar T.last.p hW (targetModels T.last)) ≫
      moduleCartesianCompositionMap T.leftOuter T.leftInner.composite T.innerToFirst
        T.isPullback_leftInner T.leftInner_j_innerToFirst Λ hX hZ hW hInner
        (targetModels T.last) (totalModels T.leftOuter.composite) =
      (moduleCompactifiedCompositionAmbientIso (f ≫ g) h Λ T.leftOuter).hom :=
  moduleCartesianFirstComparison (f ≫ g) h Λ T.leftOuter T.leftInner.composite
    T.innerToFirst T.isPullback_leftInner T.leftIntermediateRefinement
    T.isPullback_leftIntermediateComparison.flip T.leftInner_j_innerToFirst
end Left

section Right
variable [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (g ≫ h),
    HasDerivedCategory.{wGH} (ModuleSheaf C.Xbar Λ)]
  [totalModels : ∀ C : Hom.DenseCompactification (f ≫ (g ≫ h)),
    HasDerivedCategory.{wFGH} (ModuleSheaf C.Xbar Λ)]
  [hFirst : HasDerivedCategory.{wR} (ModuleSheaf T.leftInner.first.Xbar Λ)]

/-- The right raw outer route is attached by the literal first pullback refinement map. -/
theorem moduleTripleRightFirstComparison :
    Functor.whiskerRight
        (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY
          T.leftInner.first T.rightOuter.first T.firstRefinement
          hFirst (firstModels T.rightOuter.first))
        (@moduleDerivedLowerShriek Y T.tail.composite.Xbar T.tail.composite.j _ Λ _ hY
            (targetModels T.tail.composite) ⋙
          @moduleDerivedDirectImage W Λ _ T.tail.composite.Xbar T.tail.composite.p hW
            (targetModels T.tail.composite)) ≫
      moduleCartesianCompositionMap T.rightOuter T.leftInner.first
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.isPullback_first
        (tripleFirstOpenEquality T) Λ hX hY hW hFirst
        (targetModels T.tail.composite) (totalModels T.rightOuter.composite) =
      (moduleCompactifiedCompositionAmbientIso f (g ≫ h) Λ T.rightOuter).hom :=
  moduleCartesianFirstComparison f (g ≫ h) Λ T.rightOuter T.leftInner.first
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.isPullback_first T.firstRefinement
    T.isPullback_firstComparison.flip (tripleFirstOpenEquality T)
end Right

end AlgebraicGeometry.Scheme.EtaleCohomology
