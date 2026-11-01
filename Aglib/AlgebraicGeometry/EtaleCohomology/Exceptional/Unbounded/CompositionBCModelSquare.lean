/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBaseChangeModel
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBCRefinementRaw
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModelMaps
public import Aglib.CategoryTheory.Functor.ImageCompositionExchangeActual

/-! # Actual full-unbounded model composition and original commuting exchange -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wX' wY' wZ' wF wG wH wF' wG' wH'
variable {X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact f'] [QuasiCompact g']
  (C : Hom.CompactifiedComposition f g) (D : Hom.CompactifiedComposition f' g')
  (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z)
  (qF : D.first.Xbar ⟶ C.first.Xbar)
  (qG : D.targetCompactification.Xbar ⟶ C.targetCompactification.Xbar)
  (qH : D.sourceCompactification.Xbar ⟶ C.sourceCompactification.Xbar)
  (sqF : IsPullback a D.first.j C.first.j qF)
  (sqG : IsPullback b D.targetCompactification.j C.targetCompactification.j qG)
  (sqH : IsPullback a D.sourceCompactification.j C.sourceCompactification.j qH)
  (sqM : IsPullback qF D.middleOpen C.middleOpen qH)
  (hpF : D.first.p ≫ b = qF ≫ C.first.p)
  (hpG : D.targetCompactification.p ≫ c = qG ≫ C.targetCompactification.p)
  (hpH : D.sourceCompactification.p ≫ qG = qH ≫ C.sourceCompactification.p)
  (hpT : D.composite.p ≫ c = qH ≫ C.composite.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [hY' : HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [hZ' : HasDerivedCategory.{wZ'} (ModuleSheaf Z' Λ)]
  [fm : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf E.Xbar Λ)]
  [gm : ∀ E : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf E.Xbar Λ)]
  [hm : ∀ E : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wH} (ModuleSheaf E.Xbar Λ)]
  [fm' : ∀ E : Hom.DenseCompactification f',
    HasDerivedCategory.{wF'} (ModuleSheaf E.Xbar Λ)]
  [gm' : ∀ E : Hom.DenseCompactification g',
    HasDerivedCategory.{wG'} (ModuleSheaf E.Xbar Λ)]
  [hm' : ∀ E : Hom.DenseCompactification (f' ≫ g'),
    HasDerivedCategory.{wH'} (ModuleSheaf E.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf C.first.Xbar Λ`. -/
local instance unboundedCompositionBCModelF : HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar
  Λ) :=
  fm C.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance unboundedCompositionBCModelG :
    HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  gm C.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance unboundedCompositionBCModelH :
    HasDerivedCategory.{wH} (ModuleSheaf C.sourceCompactification.Xbar Λ) := hm C.composite
/-- The local derived-category model on `ModuleSheaf D.first.Xbar Λ`. -/
local instance unboundedCompositionBCModelF' : HasDerivedCategory.{wF'} (ModuleSheaf
  D.first.Xbar Λ) :=
  fm' D.first
/-- The local derived-category model on `ModuleSheaf D.targetCompactification.Xbar Λ`. -/
local instance unboundedCompositionBCModelG' :
    HasDerivedCategory.{wG'} (ModuleSheaf D.targetCompactification.Xbar Λ) :=
  gm' D.targetCompactification
/-- The local derived-category model on `ModuleSheaf D.sourceCompactification.Xbar Λ`. -/
local instance unboundedCompositionBCModelH' :
    HasDerivedCategory.{wH'} (ModuleSheaf D.sourceCompactification.Xbar Λ) := hm' D.composite


variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
include sqM hpH in
omit [QuasiCompact f] [QuasiCompact f'] in
/-- The actual original unbounded κ satisfies the actual original model law. -/
theorem moduleUnboundedCompactifiedCompositionIso_commutingExchange :
    CompositionExchangeEquation
      (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ)
      (moduleUnboundedCompactifiedCompositionIso f' g' Λ D N hN hΛ)
      (moduleUnboundedRawCommutingSquareMap C.first.toCompactification
        D.first.toCompactification a qF b sqF hpF Λ)
      (moduleUnboundedRawCommutingSquareMap C.targetCompactification.toCompactification
        D.targetCompactification.toCompactification b qG c sqG hpG Λ)
      (moduleUnboundedRawCommutingSquareMap C.composite.toCompactification
        D.composite.toCompactification a qH c sqH hpT Λ) :=
  imageCompositionExchange_actual
    (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
      C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
    (moduleUnboundedProperOpenMate D.first.p D.middleOpen D.targetCompactification.j
      D.sourceCompactification.p D.isPullback_middleOpen.flip Λ)
    (moduleUnboundedCompactifiedCompositionOpenIso f g Λ C)
    (moduleUnboundedCompactifiedCompositionOpenIso f' g' Λ D)
    (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
      C.sourceCompactification.p).symm
    (moduleUnboundedDerivedDirectImageCompIso Λ D.targetCompactification.p
      D.sourceCompactification.p).symm
    (moduleUnboundedDerivedBaseChangeMap Λ C.first.p D.first.p b qF hpF)
    (moduleUnboundedDerivedBaseChangeMap Λ C.targetCompactification.p
      D.targetCompactification.p c qG hpG)
    (moduleUnboundedDerivedBaseChangeMap Λ C.composite.p D.composite.p c qH hpT)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a D.first.j C.first.j qF sqF Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso b D.targetCompactification.j
      C.targetCompactification.j qG sqG Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a D.sourceCompactification.j
      C.sourceCompactification.j qH sqH Λ)
    (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso f' g' Λ D N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso_formula f g Λ C N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso_formula f' g' Λ D N hN hΛ)
    (moduleUnboundedCompactifiedComposition_exchange Λ
      C.first.j C.middleOpen C.sourceCompactification.j C.first.p
      C.targetCompactification.j C.sourceCompactification.p C.targetCompactification.p
      D.first.j D.middleOpen D.sourceCompactification.j D.first.p
      D.targetCompactification.j D.sourceCompactification.p D.targetCompactification.p
      C.first_j_middleOpen D.first_j_middleOpen
      C.isPullback_middleOpen.flip D.isPullback_middleOpen.flip
      a qF qH b qG c sqF sqH sqM sqG hpF hpH hpG hpT)

end AlgebraicGeometry.Scheme.EtaleCohomology
