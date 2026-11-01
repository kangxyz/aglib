/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.LeftUnitSupplied
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.LeftUnitTotalComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsionRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitIdentityValue

/-! # The original supplied left-unit triangle in the native torsion subcategory -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
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


/-- The supplied source transition is the actual original first refinement. -/
abbrev moduleLeftUnitFirstTorsionIso :=
  moduleCompactificationSingleTorsionTransition (hX := hX) (hS := hX) Λ
    (Hom.CompactifiedComposition.leftUnitFirstRefinement C)
    (firstModels (Hom.CompactifiedComposition.leftUnit C).first) hX

/-- The supplied total transition is the actual original identity ambient refinement. -/
abbrev moduleLeftUnitTotalTorsionIso :=
  moduleCompactificationSingleTorsionTransition (hX := hX) (hS := hY) Λ
    (Hom.CompactifiedComposition.leftUnitTotalRefinement C)
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C)

/-- The original supplied left-unit triangle, with no change to the binary compositor. -/
theorem moduleLeftUnitTorsionSupplied :
    Functor.isoWhiskerRight (moduleLeftUnitFirstTorsionIso f Λ C)
        (moduleCompactificationTorsionFunctor f Λ C) ≪≫
      moduleCompactifiedCompositionIso (𝟙 X) f Λ (Hom.CompactifiedComposition.leftUnit C) =
    Functor.isoWhiskerRight (moduleSingleIdentityValueIso X Λ hX hX)
        (moduleCompactificationTorsionFunctor f Λ C) ≪≫
      Functor.leftUnitor (moduleCompactificationTorsionFunctor f Λ C) ≪≫
      moduleLeftUnitTotalTorsionIso f Λ C := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  change
    (((moduleCompactificationTorsionFunctor f Λ C).map
        ((moduleLeftUnitFirstTorsionIso f Λ C).hom.app K)) ≫
      (moduleCompactifiedCompositionIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C)).hom.app K).hom =
    (((moduleCompactificationTorsionFunctor f Λ C).map
        ((moduleSingleIdentityValueIso X Λ hX hX).hom.app K)) ≫
      (𝟙 ((moduleCompactificationTorsionFunctor f Λ C).obj K) ≫
        (moduleLeftUnitTotalTorsionIso f Λ C).hom.app K)).hom
  have hi : 𝟙 ((moduleCompactificationTorsionFunctor f Λ C).obj K) ≫
      (moduleLeftUnitTotalTorsionIso f Λ C).hom.app K =
      (moduleLeftUnitTotalTorsionIso f Λ C).hom.app K := Category.id_comp _
  rw [hi]
  change
    (@moduleDerivedDirectImage Y Λ _ C.Xbar C.p hY (targetModels C)).map
      ((@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C)).map
        ((moduleLeftUnitRestrictedFirstComparison C Λ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first)).app K)) ≫
      (moduleCompactifiedCompositionAmbientIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C)).hom.app K =
    (@moduleDerivedDirectImage Y Λ _ C.Xbar C.p hY (targetModels C)).map
      ((@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C)).map
        ((moduleLeftUnitRestrictedContraction Λ hX).hom.app K)) ≫
      (@moduleCompactificationMixedTransition X Y f _ Λ _ hX hY
        (Hom.DenseCompactification.ofArrowEq (Category.id_comp f)
          (Hom.CompactifiedComposition.leftUnit C).composite) C
        (Hom.CompactifiedComposition.leftUnitTotalRefinement C)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)
        (targetModels C)).app K
  have ht := congrArg
    (fun τ => (@moduleDerivedDirectImage Y Λ _ C.Xbar C.p hY (targetModels C)).map
      ((@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C)).map
        ((moduleLeftUnitRestrictedContraction Λ hX).hom.app K)) ≫ τ.app K)
    (moduleLeftUnitTotalMixedTransition C Λ hX hY
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C))
  exact (congrArg (fun τ => τ.app K) (moduleLeftUnitSuppliedEquation f Λ C)).trans ht.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
