/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.CompositionBCRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeLiftFormula

/-! # The original commuting exchange on native torsion-valued models -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wX' wT wM wN

section Component
variable {X S X' T : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ T}
  (C : Hom.Compactification f) (D : Hom.Compactification f')
  (a : X' ⟶ X) (q : D.Xbar ⟶ C.Xbar) (b : T ⟶ S)
  (hj : IsPullback a D.j C.j q) (hp : D.p ≫ b = q ≫ C.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]

/-- The complete original restriction formula, without expanding native components. -/
theorem moduleRawCommutingSquareMap_formula :
    CompositeExchangeLiftFormula (moduleTorsionCohomologyPlus X Λ)
      (moduleTorsionCohomologyPlus X' Λ) (moduleDerivedInverseImage Λ a)
      (moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p)
      (moduleDerivedLowerShriek D.j Λ ⋙ moduleDerivedDirectImage Λ D.p)
      (moduleDerivedInverseImage Λ b)
      (fun L => ((moduleDerivedInverseImageTorsion a Λ).obj L).property)
      (moduleCompactifiedCommutingExchange C.j C.p D.j D.p a q b hj hp Λ)
      (moduleRawCommutingSquareMap C D a q b hj hp Λ) :=
  compositeExchange_lift_formula (moduleTorsionCohomologyPlus X Λ)
    (moduleTorsionCohomologyPlus X' Λ) (moduleDerivedInverseImage Λ a)
    (moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p)
    (moduleDerivedLowerShriek D.j Λ ⋙ moduleDerivedDirectImage Λ D.p)
    (moduleDerivedInverseImage Λ b)
    (fun L => ((moduleDerivedInverseImageTorsion a Λ).obj L).property)
    (moduleCompactifiedCommutingExchange C.j C.p D.j D.p a q b hj hp Λ)


end Component

variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  [QuasiCompact f] [QuasiCompact f'] (C : Hom.DenseCompactification f)
  (D : Hom.DenseCompactification f') (a : X' ⟶ X) (q : D.Xbar ⟶ C.Xbar) (b : T ⟶ S)
  (hj : IsPullback a D.j C.j q) (hp : D.p ≫ b = q ≫ C.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [sourceModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification f',
    HasDerivedCategory.{wN} (ModuleSheaf E.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf C.Xbar Λ`. -/
local instance compositionBCTorsionSourceModel : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) :=
  sourceModels C
/-- The local derived-category model on `ModuleSheaf D.Xbar Λ`. -/
local instance compositionBCTorsionTargetModel : HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ) :=
  targetModels D

/-- Lift the unchanged original exchange to the native full torsion subcategories.
This definition does not assert invertibility for a merely commuting proper face. -/
def moduleCompactificationCommutingExchangeTorsion :
    moduleCompactificationTorsionFunctor f Λ C ⋙ moduleDerivedInverseImageTorsion b Λ ⟶
      moduleDerivedInverseImageTorsion a Λ ⋙ moduleCompactificationTorsionFunctor f' Λ D where
  app K := ObjectProperty.homMk
    ((moduleRawCommutingSquareMap C.toCompactification D.toCompactification a q b hj hp Λ).app K)
  naturality K L φ := by
    apply ObjectProperty.hom_ext
    exact (moduleRawCommutingSquareMap C.toCompactification D.toCompactification
      a q b hj hp Λ).naturality φ

omit [QuasiCompact f] [QuasiCompact f'] in
/-- The torsion-valued exchange retains the same original ambient component. -/
theorem moduleCompactificationCommutingExchangeTorsion_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleCompactificationCommutingExchangeTorsion f f' C D a q b hj hp Λ).app K).hom =
      (moduleRawCommutingSquareMap C.toCompactification D.toCompactification a q b hj hp Λ).app K :=
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
