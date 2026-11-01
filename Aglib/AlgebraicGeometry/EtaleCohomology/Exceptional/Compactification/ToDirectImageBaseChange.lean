/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenToDirectImageBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeOverComparisonEquation
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeToTarget

/-! # The raw compactification exchange preserves the original canonical comparison -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wS wX' wY' wT
variable {X Y S X' Y' T : Scheme.{u}}
  (j : X ⟶ Y) (p : Y ⟶ S) (j' : X' ⟶ Y') (p' : Y' ⟶ T)
  (f : X ⟶ S) (f' : X' ⟶ T) (hf : j ≫ p = f) (hf' : j' ≫ p' = f')
  (a : X' ⟶ X) (c : Y' ⟶ Y) (b : T ⟶ S)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (hj : IsPullback a j' j c) (hp : IsPullback c p' p b)
  (h : f' ≫ b = a ≫ f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Actual raw exchange and the actual structural direct-image exchange commute with b.
No properness or torsion is needed for this equality of the original maps. -/
theorem moduleCompactifiedBaseChangeMap_toDirectImage :
    CompositeExchangeToTargetEquation
      (moduleDerivedLowerShriekToDirectImage Λ j)
      (moduleDerivedLowerShriekToDirectImage Λ j')
      (moduleDerivedDirectImageOverIso Λ f p j hf)
      (moduleDerivedDirectImageOverIso Λ f' p' j' hf')
      (moduleDerivedBaseChangeMap Λ p p' b c hp.w.symm)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j c hj Λ)
      (moduleDerivedBaseChangeMap Λ f f' b a h) :=
  compositeExchange_toTarget
    (moduleDerivedLowerShriekToDirectImage Λ j)
    (moduleDerivedLowerShriekToDirectImage Λ j')
    (moduleDerivedDirectImageOverIso Λ f p j hf)
    (moduleDerivedDirectImageOverIso Λ f' p' j' hf')
    (moduleDerivedBaseChangeMap Λ p p' b c hp.w.symm)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j c hj Λ)
    (moduleDerivedBaseChangeMap Λ j j' c a hj.w.symm)
    (moduleDerivedBaseChangeMap Λ f f' b a h)
    (moduleDerivedLowerShriekToDirectImage_baseChange Λ a j' j c hj)
    (moduleDerivedBaseChangeMap_over_comp_equation Λ f p j hf f' p' j' hf'
      b a c h hp.w.symm hj.w.symm)
end AlgebraicGeometry.Scheme.EtaleCohomology
