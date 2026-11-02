/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.PullbackCoherence
public import Aglib.CategoryTheory.Adjunction.UnitComparisonCoherence

/-! # Identity normalization for original raw compactification transitions -/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wS

variable {X Y S : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  (sq : IsPullback j (𝟙 X) (𝟙 Y) j) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]

/-- Identity coherence of the original pullback comparison without a density assumption. -/
theorem moduleDerivedProperRefinementPullbackIso_id :
    moduleDerivedProperRefinementPullbackIso j j (𝟙 Y) sq Λ =
      Functor.isoWhiskerLeft (moduleDerivedLowerShriek j Λ)
        (moduleDerivedInverseImageIdIso Λ Y) ≪≫
        Functor.rightUnitor (moduleDerivedLowerShriek j Λ) :=
  Functor.rightDerivedFunctorPlusPullbackIso_id
    (moduleLowerShriek j Λ) (moduleInverseImage (𝟙 Y) Λ)
    (moduleLowerShriekCartesianIdentityIso j j (𝟙 Y) sq.flip Λ)
    (moduleInverseImageIdIso Λ Y)
    (moduleLowerShriekCartesianIdentityIso_id j sq.flip Λ)

/-- The original unit-induced raw identity refinement has its original normalization. -/
theorem moduleDerivedProperRefinementComparison_id :
    moduleDerivedProperRefinementComparison j j (𝟙 Y) sq Λ ≫
      Functor.whiskerLeft (moduleDerivedLowerShriek j Λ)
        (moduleDerivedDirectImageIdIso Λ Y).hom ≫
      (Functor.rightUnitor (moduleDerivedLowerShriek j Λ)).hom =
    𝟙 (moduleDerivedLowerShriek j Λ) := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, moduleDerivedProperRefinementComparison_app]
  erw [Category.comp_id]
  exact adjunctionUnitComparison_id (moduleDerivedAdjunction Λ (𝟙 Y))
    (moduleDerivedProperRefinementPullbackIso j j (𝟙 Y) sq Λ)
    (moduleDerivedInverseImageIdIso Λ Y) (moduleDerivedDirectImageIdIso Λ Y)
    (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ Y)
    (moduleDerivedProperRefinementPullbackIso_id j sq Λ) K

variable (p : Y ⟶ S) [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The original over-base direct compositor has its native identity value. -/
theorem moduleDerivedDirectImageOverIso_id :
    moduleDerivedDirectImageOverIso Λ p p (𝟙 Y) (Category.id_comp p) =
      Functor.isoWhiskerRight (moduleDerivedDirectImageIdIso Λ Y)
        (moduleDerivedDirectImage Λ p) ≪≫ Functor.leftUnitor (moduleDerivedDirectImage Λ p) :=
  inverse_compositor_normalization (moduleDerivedDirectImageCompIso Λ p (𝟙 Y)) _ _
    (moduleDerivedDirectImageCompIso_comp_id Λ p)

/-- The actual ambient identity transition is the identity, before any torsion restriction. -/
theorem moduleRawImageComparison_id :
    imageComparison (moduleDerivedProperRefinementComparison j j (𝟙 Y) sq Λ)
      (moduleDerivedDirectImageOverIso Λ p p (𝟙 Y) (Category.id_comp p)) =
      𝟙 (moduleDerivedLowerShriek j Λ ⋙ moduleDerivedDirectImage Λ p) :=
  imageComparison_id (moduleDerivedProperRefinementComparison j j (𝟙 Y) sq Λ)
    (moduleDerivedDirectImageIdIso Λ Y)
    (moduleDerivedDirectImageOverIso Λ p p (𝟙 Y) (Category.id_comp p))
    (moduleDerivedProperRefinementComparison_id j sq Λ)
    (moduleDerivedDirectImageOverIso_id Λ p)

end AlgebraicGeometry.Scheme.EtaleCohomology
