/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitFace
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence
public import Aglib.CategoryTheory.Functor.ImageSourceIdentity

/-! # Original first-refinement normalization in the left-unit triangle

The identity factor here is the endpoint model. Comparison with an independent
identity middle model uses the separate original mixed-model family transport.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA
variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original over-base compositor at the identity target has its original unit value. -/
theorem moduleDerivedDirectImageOverIso_identityTarget
    {A X : Scheme.{u}} (q : A ⟶ X)
    [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    moduleDerivedDirectImageOverIso Λ q (𝟙 X) q (Category.comp_id q) =
      Functor.isoWhiskerLeft (moduleDerivedDirectImage Λ q)
          (moduleDerivedDirectImageIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleDerivedDirectImage Λ q) := by
  rw [moduleDerivedDirectImageOverIso, ← moduleDerivedDirectImageCompIso_id_comp]
  simp only [Iso.symm_self_id_assoc]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f)
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.leftUnit C).first.Xbar Λ))

/-- The first original refinement comparison has exactly the source identity normalization. -/
theorem moduleLeftUnitFirstComparison_identityTarget :
    CategoryTheory.imageComparison
      (@moduleDerivedRefinementComparison X X (𝟙 X) _
        (Hom.CompactifiedComposition.leftUnit C).first
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX)
      (@moduleDerivedRefinementDirectImageIso Λ _ X X (𝟙 X) hX
        (Hom.CompactifiedComposition.leftUnit C).first
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (Hom.CompactifiedComposition.leftUnitFirstRefinement C) hA hX) =
      Functor.whiskerLeft (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
        (@moduleDerivedDirectImageIdIso Λ _ X hX).hom ≫
      (Functor.rightUnitor (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)).hom ≫
      (@moduleDerivedRefinementComparison X X (𝟙 X) _
        (Hom.CompactifiedComposition.leftUnit C).first
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX) :=
  imageComparison_identityTarget _ (@moduleDerivedDirectImageIdIso Λ _ X hX) _
    (@moduleDerivedDirectImageOverIso_identityTarget Λ _
      (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
      (Hom.CompactifiedComposition.leftUnit C).first.p hA hX)

end AlgebraicGeometry.Scheme.EtaleCohomology
