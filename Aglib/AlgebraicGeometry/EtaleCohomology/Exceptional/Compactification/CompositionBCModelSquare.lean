/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.CompositionBaseChangeModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.CompositionBCTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionModelMaps
public import Aglib.CategoryTheory.Functor.ImageCompositionExchangeRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters

/-! # Original torsion-valued model composition and arbitrary exchange -/

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
local instance compositionBCModelF : HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) :=
  fm C.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance compositionBCModelG :
    HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  gm C.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance compositionBCModelH :
    HasDerivedCategory.{wH} (ModuleSheaf C.sourceCompactification.Xbar Λ) := hm C.composite
/-- The local derived-category model on `ModuleSheaf D.first.Xbar Λ`. -/
local instance compositionBCModelF' : HasDerivedCategory.{wF'} (ModuleSheaf D.first.Xbar Λ) :=
  fm' D.first
/-- The local derived-category model on `ModuleSheaf D.targetCompactification.Xbar Λ`. -/
local instance compositionBCModelG' :
    HasDerivedCategory.{wG'} (ModuleSheaf D.targetCompactification.Xbar Λ) :=
  gm' D.targetCompactification
/-- The local derived-category model on `ModuleSheaf D.sourceCompactification.Xbar Λ`. -/
local instance compositionBCModelH' :
    HasDerivedCategory.{wH'} (ModuleSheaf D.sourceCompactification.Xbar Λ) := hm' D.composite

include sqM hpH in
omit [QuasiCompact f] [QuasiCompact f'] in
/-- The accepted original torsion compositor satisfies the model exchange law.
No desired square is a premise, and the six middle model families are independent. -/
theorem moduleCompactifiedCompositionIso_commutingExchange :
    CompositionExchangeEquation
      (moduleCompactifiedCompositionIso f g Λ C)
      (moduleCompactifiedCompositionIso f' g' Λ D)
      (moduleCompactificationCommutingExchangeTorsion f f' C.first D.first a qF b sqF hpF Λ)
      (moduleCompactificationCommutingExchangeTorsion g g' C.targetCompactification
        D.targetCompactification b qG c sqG hpG Λ)
      (moduleCompactificationCommutingExchangeTorsion (f ≫ g) (f' ≫ g')
        C.composite D.composite a qH c sqH hpT Λ) :=
  imageCompositionExchange_restrict
    (moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
      C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip)
    (moduleProperOpenMate Λ D.targetCompactification.j D.middleOpen
      D.first.p D.sourceCompactification.p D.isPullback_middleOpen.flip)
    (moduleCompactifiedCompositionOpenIso f g Λ C)
    (moduleCompactifiedCompositionOpenIso f' g' Λ D)
    (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p C.sourceCompactification.p).symm
    (moduleDerivedDirectImageCompIso Λ D.targetCompactification.p D.sourceCompactification.p).symm
    (moduleDerivedBaseChangeMap Λ C.first.p D.first.p b qF hpF)
    (moduleDerivedBaseChangeMap Λ C.targetCompactification.p D.targetCompactification.p c qG hpG)
    (moduleDerivedBaseChangeMap Λ C.composite.p D.composite.p c qH hpT)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a D.first.j C.first.j qF sqF Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso b D.targetCompactification.j
      C.targetCompactification.j qG sqG Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a D.sourceCompactification.j
      C.sourceCompactification.j qH sqH Λ)
    (moduleTorsionCohomologyPlus X Λ) (moduleTorsionCohomologyPlus Y Λ)
    (moduleTorsionCohomologyPlus Z Λ) (moduleTorsionCohomologyPlus X' Λ)
    (moduleTorsionCohomologyPlus Y' Λ) (moduleTorsionCohomologyPlus Z' Λ)
    (fun K => ((moduleCompactificationTorsionFunctor f Λ C.first).obj K).property)
    (fun K => ((moduleCompactificationTorsionFunctor g Λ C.targetCompactification).obj K).property)
    (fun K => ((moduleCompactificationTorsionFunctor (f ≫ g) Λ C.composite).obj K).property)
    (fun K => ((moduleCompactificationTorsionFunctor f' Λ D.first).obj K).property)
    (fun K => ((moduleCompactificationTorsionFunctor g' Λ D.targetCompactification).obj K).property)
    (fun K => ((moduleCompactificationTorsionFunctor (f' ≫ g') Λ D.composite).obj K).property)
    (fun K => ((moduleDerivedInverseImageTorsion a Λ).obj K).property)
    (fun K => ((moduleDerivedInverseImageTorsion b Λ).obj K).property)
    (fun K => ((moduleDerivedInverseImageTorsion c Λ).obj K).property)
    (moduleCompactifiedCompositionIso f g Λ C)
    (moduleCompactifiedCompositionIso f' g' Λ D)
    (moduleCompactifiedCompositionAmbientIso f g Λ C).hom
    (moduleCompactifiedCompositionAmbientIso f' g' Λ D).hom rfl rfl
    (moduleCompactifiedCompositionAmbientIso_formula f g Λ (C := C))
    (moduleCompactifiedCompositionAmbientIso_formula f' g' Λ (C := D))
    (moduleRawCommutingSquareMap C.first.toCompactification D.first.toCompactification
      a qF b sqF hpF Λ)
    (moduleRawCommutingSquareMap C.targetCompactification.toCompactification
      D.targetCompactification.toCompactification b qG c sqG hpG Λ)
    (moduleRawCommutingSquareMap C.composite.toCompactification D.composite.toCompactification
      a qH c sqH hpT Λ)
    (moduleRawCommutingSquareMap_formula C.first.toCompactification D.first.toCompactification
      a qF b sqF hpF Λ)
    (moduleRawCommutingSquareMap_formula C.targetCompactification.toCompactification
      D.targetCompactification.toCompactification b qG c sqG hpG Λ)
    (moduleRawCommutingSquareMap_formula C.composite.toCompactification
      D.composite.toCompactification a qH c sqH hpT Λ)
    (moduleCompactificationCommutingExchangeTorsion f f' C.first D.first a qF b sqF hpF Λ)
    (moduleCompactificationCommutingExchangeTorsion g g' C.targetCompactification
      D.targetCompactification b qG c sqG hpG Λ)
    (moduleCompactificationCommutingExchangeTorsion (f ≫ g) (f' ≫ g')
      C.composite D.composite a qH c sqH hpT Λ) rfl rfl rfl
    (moduleCompactifiedComposition_exchange Λ
      C.first.j C.middleOpen C.sourceCompactification.j C.first.p
      C.targetCompactification.j C.sourceCompactification.p C.targetCompactification.p
      D.first.j D.middleOpen D.sourceCompactification.j D.first.p
      D.targetCompactification.j D.sourceCompactification.p D.targetCompactification.p
      C.first_j_middleOpen D.first_j_middleOpen
      C.isPullback_middleOpen.flip D.isPullback_middleOpen.flip
      a qF qH b qG c sqF sqH sqM sqG hpF hpH hpG hpT)

end AlgebraicGeometry.Scheme.EtaleCohomology
