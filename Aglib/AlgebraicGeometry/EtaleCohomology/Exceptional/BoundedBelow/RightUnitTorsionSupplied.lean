/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RightUnitSuppliedComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsionRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitIdentityValue

/-! # The original supplied right-unit triangle in the native torsion subcategory -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification (𝟙 Y),
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification (f ≫ 𝟙 Y),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

/-- The original total-to-first torsion transition along the actual dense refinement. -/
abbrev moduleRightUnitTotalTorsionIso :=
  moduleCompactificationSingleTorsionTransition (hX := hX) (hS := hY) Λ
    (Hom.CompactifiedComposition.rightUnitFirstToTotalRefinement C)
    (firstModels (Hom.CompactifiedComposition.rightUnit C).first)
    (compositeModels (Hom.CompactifiedComposition.rightUnit C).composite)

/-- Torsion recording preserves the literal supplied right-unit triangle and original epsilon. -/
theorem moduleRightUnitTorsionSupplied :
    moduleCompactifiedCompositionIso
        (firstModels := firstModels) (secondModels := targetModels)
        (compositeModels := compositeModels) f (𝟙 Y) Λ
        (Hom.CompactifiedComposition.rightUnit C) ≪≫
      moduleRightUnitTotalTorsionIso
        (firstModels := firstModels) (compositeModels := compositeModels) f Λ C =
    Functor.isoWhiskerLeft
        ((@moduleCompactificationTorsionFunctor _ _ f Λ _ _ _
          (Hom.CompactifiedComposition.rightUnit C).first
          (firstModels (Hom.CompactifiedComposition.rightUnit C).first)))
        (moduleSingleIdentityValueIso Y Λ hY
          (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification)) ≪≫
      Functor.rightUnitor
        ((@moduleCompactificationTorsionFunctor _ _ f Λ _ _ _
          (Hom.CompactifiedComposition.rightUnit C).first
          (firstModels (Hom.CompactifiedComposition.rightUnit C).first))) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  change
    (moduleCompactifiedCompositionAmbientIso
      (firstModels := firstModels) (secondModels := targetModels)
      (compositeModels := compositeModels) f (𝟙 Y) Λ
      (Hom.CompactifiedComposition.rightUnit C)).hom.app K ≫
      (moduleRightUnitSuppliedRefinement
        (firstModels := firstModels) (compositeModels := compositeModels) f Λ C).app K =
    (moduleRightUnitSuppliedContraction
      (firstModels := firstModels) (targetModels := targetModels) f Λ C).hom.app K ≫ 𝟙 _
  have h := congrArg (fun τ => τ.app K)
    (moduleRightUnitSuppliedMixedEquation
      (firstModels := firstModels) (targetModels := targetModels)
      (compositeModels := compositeModels) f Λ C)
  exact h.trans (Category.comp_id _).symm


end AlgebraicGeometry.Scheme.EtaleCohomology
