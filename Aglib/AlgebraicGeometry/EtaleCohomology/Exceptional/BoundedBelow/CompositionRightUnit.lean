/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RightUnitTorsionSupplied
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RightUnitChosenTarget
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Composition
public import Aglib.CategoryTheory.Functor.ChosenRightUnit

/-! # The right-unit law for the original choice-independent exceptional compositor -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification (𝟙 Y),
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification (f ≫ 𝟙 Y),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]

/-- The actual chosen compositor has the original epsilon as its right unit. -/
theorem moduleExceptionalCompositionIso_comp_id :
    moduleExceptionalCompositionIso f (𝟙 Y) Λ ≪≫
      moduleExceptionalDirectImagePlusTorsionCongr Λ hX hY (Category.comp_id f)
        compositeModels firstModels =
    Functor.isoWhiskerLeft (moduleExceptionalDirectImagePlusTorsion f Λ)
        (moduleExceptionalIdentityIso Y Λ) ≪≫
      Functor.rightUnitor (moduleExceptionalDirectImagePlusTorsion f Λ) := by
  let C := moduleExceptionalCompactification f
  let χI := moduleExceptionalDirectImagePlusTorsionIso (𝟙 Y) Λ
    (Hom.CompactifiedComposition.rightUnit C).targetCompactification
  let ε := moduleSingleIdentityValueIso Y Λ hY
    (targetModels (Hom.CompactifiedComposition.rightUnit C).targetCompactification)
  have hs := chosenRightUnit
    (moduleExceptionalCompositionIso f (𝟙 Y) Λ)
    (moduleExceptionalDirectImagePlusTorsionIso f Λ
      (Hom.CompactifiedComposition.rightUnit C).first)
    χI
    (moduleExceptionalDirectImagePlusTorsionIso (f ≫ 𝟙 Y) Λ
      (Hom.CompactifiedComposition.rightUnit C).composite)
    (moduleCompactifiedCompositionIso f (𝟙 Y) Λ (Hom.CompactifiedComposition.rightUnit C))
    (moduleRightUnitTotalTorsionIso (firstModels := firstModels)
      (compositeModels := compositeModels) f Λ C)
    ε
    (moduleExceptionalDirectImagePlusTorsionCongr Λ hX hY (Category.comp_id f)
      compositeModels firstModels)
    (moduleExceptionalCompositionIso_comparison f (𝟙 Y) Λ
      (Hom.CompactifiedComposition.rightUnit C)).symm
    (moduleRightUnitTorsionSupplied (firstModels := firstModels)
      (targetModels := targetModels) (compositeModels := compositeModels) f Λ C)
    (moduleRightUnitChosenTargetSquare f Λ C)
  have hε : χI ≪≫ ε = moduleExceptionalIdentityIso Y Λ :=
    (moduleExceptionalIdentityIso_singleValue (models := targetModels) Y Λ hY).symm
  exact hs.trans (congrArg
    (fun e => Functor.isoWhiskerLeft (moduleExceptionalDirectImagePlusTorsion f Λ) e ≪≫
      Functor.rightUnitor (moduleExceptionalDirectImagePlusTorsion f Λ)) hε)

end AlgebraicGeometry.Scheme.EtaleCohomology
