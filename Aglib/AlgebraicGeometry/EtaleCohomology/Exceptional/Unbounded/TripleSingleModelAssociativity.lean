/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCartesianCompositionIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleSingleModelMaps

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
local instance unboundedTripleSingleFinalA0 :
    HasDerivedCategory.{wF} (ModuleSheaf T.leftInner.first.Xbar Λ) :=
  fModels T.leftInner.first
/-- The local derived-category model on `ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ`.
-/
local instance unboundedTripleSingleFinalA1 :
    HasDerivedCategory.{wFG} (ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ) :=
  fgModels T.leftInner.composite
/-- The local derived-category model on `ModuleSheaf T.first.Xbar Λ`. -/
local instance unboundedTripleSingleFinalA2 :
    HasDerivedCategory.{wL} (ModuleSheaf T.first.Xbar Λ) :=
  leftModels T.leftOuter.composite
/-- The local derived-category model on `ModuleSheaf T.tail.first.Xbar Λ`. -/
local instance unboundedTripleSingleFinalB0 :
    HasDerivedCategory.{wG} (ModuleSheaf T.tail.first.Xbar Λ) := gModels T.tail.first
/-- The local derived-category model on `ModuleSheaf T.middle.Xbar Λ`. -/
local instance unboundedTripleSingleFinalB1 :
    HasDerivedCategory.{wGH} (ModuleSheaf T.middle.Xbar Λ) := ghModels T.tail.composite
/-- The local derived-category model on `ModuleSheaf T.last.Xbar Λ`. -/
local instance unboundedTripleSingleFinalC :
    HasDerivedCategory.{wH} (ModuleSheaf T.last.Xbar Λ) := hModels T.last
local instance unboundedTripleSingleFinalLeftOpen : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion
local instance unboundedTripleSingleFinalRightOpen : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

/-- The actual seven-family single-value compositors associate through their original
whole Cartesian maps and the original total-arrow transition. -/
theorem moduleUnboundedTripleSingleModelAssociativity :
    OpenCompositionEquation
      (moduleUnboundedTripleSingleInnerIso T Λ N hN hΛ)
      (moduleUnboundedTripleSingleLeftIso T Λ N hN hΛ ≪≫
        (moduleUnboundedTripleSingleTotalIso T Λ N hN hΛ).symm)
      (moduleUnboundedTripleSingleRightIso T Λ N hN hΛ)
      (moduleUnboundedTripleSingleTailIso T Λ N hN hΛ) :=
  imageCartesianCompositionIso_of_formulas
    (moduleUnboundedTripleSingleInnerIso T Λ N hN hΛ)
    (moduleUnboundedTripleSingleLeftIso T Λ N hN hΛ)
    (moduleUnboundedTripleSingleRightIso T Λ N hN hΛ)
    (moduleUnboundedTripleSingleTailIso T Λ N hN hΛ)
    (moduleUnboundedTripleSingleTotalIso T Λ N hN hΛ)
    (eqToIso (congrArg (fun q : T.first.Xbar ⟶ W => moduleUnboundedDerivedDirectImage Λ q)
      (Category.assoc T.first.p T.middle.p T.last.p).symm))
    (moduleUnboundedTripleLeftInnerMap T Λ) (moduleUnboundedTripleLeftOuterMap T Λ)
    (moduleUnboundedTripleRightOuterMap T Λ) (moduleUnboundedTripleTailMap T Λ)
    (moduleUnboundedTripleSingleInnerIso_formula T Λ N hN hΛ)
    (moduleUnboundedTripleSingleLeftIso_formula T Λ N hN hΛ)
    (moduleUnboundedTripleSingleRightIso_formula T Λ N hN hΛ)
    (moduleUnboundedTripleSingleTailIso_formula T Λ N hN hΛ)
    (moduleUnboundedTripleSingleTotalIso_formula T Λ N hN hΛ)
    (moduleUnboundedTripleCartesianComposition T Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
