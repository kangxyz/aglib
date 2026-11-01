/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransitionCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementPullbackCoherence
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
theorem moduleUnboundedDerivedProperRefinementPullbackIso_id :
    moduleUnboundedDerivedProperRefinementPullbackIso j j (𝟙 Y) sq Λ =
      Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek j Λ)
        (moduleUnboundedDerivedInverseImageIdIso Λ Y) ≪≫
        Functor.rightUnitor (moduleUnboundedDerivedLowerShriek j Λ) :=
  Functor.mapDerivedCategoryTriangleIso_id
    (moduleLowerShriek j Λ) (moduleInverseImage (𝟙 Y) Λ)
    (moduleLowerShriekCartesianIdentityIso j j (𝟙 Y) sq.flip Λ)
    (moduleInverseImageIdIso Λ Y)
    (moduleLowerShriekCartesianIdentityIso_id j sq.flip Λ)

/-- The original unit-induced raw identity refinement has its original normalization. -/
theorem moduleUnboundedDerivedProperRefinementComparison_id :
    moduleUnboundedDerivedProperRefinementComparison j j (𝟙 Y) sq Λ ≫
      Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek j Λ)
        (moduleUnboundedDerivedDirectImageIdIso Λ Y).hom ≫
      (Functor.rightUnitor (moduleUnboundedDerivedLowerShriek j Λ)).hom =
    𝟙 (moduleUnboundedDerivedLowerShriek j Λ) := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, moduleUnboundedDerivedProperRefinementComparison_app]
  erw [Category.comp_id]
  exact adjunctionUnitComparison_id (moduleUnboundedDerivedAdjunction Λ (𝟙 Y))
    (moduleUnboundedDerivedProperRefinementPullbackIso j j (𝟙 Y) sq Λ)
    (moduleUnboundedDerivedInverseImageIdIso Λ Y) (moduleUnboundedDerivedDirectImageIdIso Λ Y)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ Y)
    (moduleUnboundedDerivedProperRefinementPullbackIso_id j sq Λ) K

variable (p : Y ⟶ S) [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The original over-base direct compositor has its native identity value. -/
theorem moduleUnboundedDerivedDirectImageOverIso_id :
    moduleUnboundedDerivedDirectImageOverIso Λ p p (𝟙 Y) (Category.id_comp p) =
      Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageIdIso Λ Y)
        (moduleUnboundedDerivedDirectImage Λ p) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedDirectImage Λ p) :=
  inverse_compositor_normalization (moduleUnboundedDerivedDirectImageCompIso Λ p (𝟙 Y)) _ _
    (moduleUnboundedDerivedDirectImageCompIso_comp_id Λ p)

/-- The actual ambient identity transition is the identity, before any torsion restriction. -/
theorem moduleUnboundedRawImageComparison_id :
    imageComparison (moduleUnboundedDerivedProperRefinementComparison j j (𝟙 Y) sq Λ)
      (moduleUnboundedDerivedDirectImageOverIso Λ p p (𝟙 Y) (Category.id_comp p)) =
      𝟙 (moduleUnboundedDerivedLowerShriek j Λ ⋙ moduleUnboundedDerivedDirectImage Λ p) :=
  imageComparison_id (moduleUnboundedDerivedProperRefinementComparison j j (𝟙 Y) sq Λ)
    (moduleUnboundedDerivedDirectImageIdIso Λ Y)
    (moduleUnboundedDerivedDirectImageOverIso Λ p p (𝟙 Y) (Category.id_comp p))
    (moduleUnboundedDerivedProperRefinementComparison_id j sq Λ)
    (moduleUnboundedDerivedDirectImageOverIso_id Λ p)

end AlgebraicGeometry.Scheme.EtaleCohomology
