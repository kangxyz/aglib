/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.LeftUnitTorsionSupplied
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelArrow
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Composition
public import Aglib.CategoryTheory.Functor.ChosenLeftUnit

/-! # Descent of the proved left-unit triangle through the original canonical comparisons

The identity contraction is still expressed through one endpoint-modeled
identity value. Its identification with the original independently modeled
chosen epsilon is a separate original mixed-identity normalization.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsSeparated f] [LocallyOfFiniteType f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification ((𝟙 X) ≫ f),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

include C in
/-- The original chosen compositor contracts through the original single-value comparison. -/
theorem moduleExceptionalLeftUnitContraction :
    moduleExceptionalCompositionIso (𝟙 X) f Λ ≪≫
      moduleExceptionalDirectImagePlusTorsionCongr Λ hX hY (Category.id_comp f)
        compositeModels targetModels =
    Functor.isoWhiskerRight
        (moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hX)
            (models := firstModels) (𝟙 X) Λ (Hom.DenseCompactification.ofProper (𝟙 X)) hX ≪≫
          moduleSingleIdentityValueIso X Λ hX hX)
        (moduleExceptionalDirectImagePlusTorsion f Λ) ≪≫
      Functor.leftUnitor (moduleExceptionalDirectImagePlusTorsion f Λ) := by
  apply chosenLeftUnit
    (χQ := moduleExceptionalDirectImagePlusTorsionIso (𝟙 X) Λ
      (Hom.CompactifiedComposition.leftUnit C).first)
    (χF := moduleExceptionalDirectImagePlusTorsionIso f Λ C)
    (χH := moduleExceptionalDirectImagePlusTorsionIso ((𝟙 X) ≫ f) Λ
      (Hom.CompactifiedComposition.leftUnit C).composite)
    (τ := moduleLeftUnitFirstTorsionIso f Λ C)
    (α := moduleCompactifiedCompositionIso (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C))
    (t := moduleLeftUnitTotalTorsionIso f Λ C)
  · have hs := moduleExceptionalSingleTorsionValueIso_refinement (𝟙 X) Λ
      (Hom.CompactifiedComposition.leftUnitFirstRefinement C)
      (firstModels (Hom.CompactifiedComposition.leftUnit C).first) hX
    exact hs.trans (moduleExceptionalSingleTorsionValueIso_self (𝟙 X) Λ
      (Hom.CompactifiedComposition.leftUnit C).first)
  · exact (moduleExceptionalCompositionIso_comparison (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C)).symm
  · exact moduleLeftUnitTorsionSupplied f Λ C
  · have ht := moduleExceptionalSingleTorsionValueIso_refinement f Λ
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C)
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C)
    have hc := moduleExceptionalSingleTorsionValueIso_self f Λ C
    have ht' := (congrArg (fun z => z ≪≫ moduleLeftUnitTotalTorsionIso f Λ C) hc).symm.trans ht
    have hg := moduleExceptionalSingleTorsionValueIso_congr Λ hX hY (Category.id_comp f)
      compositeModels (Hom.CompactifiedComposition.leftUnit C).composite
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) targetModels
    have htotal := congrArg
      (fun z => moduleExceptionalDirectImagePlusTorsionCongr Λ hX hY (Category.id_comp f)
        compositeModels targetModels ≪≫ z) ht'
    exact htotal.trans (hg.trans
      (moduleExceptionalSingleTorsionValueIso_self ((𝟙 X) ≫ f) Λ
        (Hom.CompactifiedComposition.leftUnit C).composite))

end AlgebraicGeometry.Scheme.EtaleCohomology
