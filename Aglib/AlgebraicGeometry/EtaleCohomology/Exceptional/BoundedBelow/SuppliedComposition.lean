/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementCube
public import Aglib.CategoryTheory.Functor.CompositionChoice
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SuppliedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Composition

/-! # The original chosen compositor on supplied compactifiable maps

This is the same compactified-tower construction and canonical comparison as
on qcqs targets. Actual supplied compactifiability replaces Nagata existence;
no qcqs assumption is imposed on a new base. The original refinement cube and
actual common towers prove independence, not a supplied compatibility field.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [Nonempty (Hom.DenseCompactification f)]
  [Nonempty (Hom.DenseCompactification g)]
  [Nonempty (Hom.DenseCompactification (f ≫ g))]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

/-- The supplied torsion comparison retains the original comparison cocycle. -/
theorem moduleExceptionalDirectImagePlusTorsionOfNonemptyIso_trans
    (C D : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusTorsionOfNonemptyIso f Λ C ≪≫
      moduleCompactificationTorsionComparison f Λ C D =
        moduleExceptionalDirectImagePlusTorsionOfNonemptyIso f Λ D :=
  moduleCompactificationTorsionComparison_trans f Λ
    (moduleExceptionalSuppliedCompactification f) C D

/-- The original tower composition, transported by the canonical comparisons. -/
def moduleExceptionalSuppliedCompositionOfTower (C : Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ⋙
      moduleExceptionalDirectImagePlusTorsionOfNonempty g Λ ≅
    moduleExceptionalDirectImagePlusTorsionOfNonempty (f ≫ g) Λ :=
  compositionPairIso
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso f Λ C.first)
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso g Λ C.targetCompactification) ≪≫
  moduleCompactifiedCompositionIso f g Λ C ≪≫
  (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso (f ≫ g) Λ C.composite).symm

/-- A genuine tower refinement does not change the transported original map. -/
theorem moduleExceptionalSuppliedCompositionOfTower_refinement
    {C D : Hom.CompactifiedComposition f g}
    (a : Hom.CompactifiedComposition.Refinement C D) :
    moduleExceptionalSuppliedCompositionOfTower f g Λ C =
      moduleExceptionalSuppliedCompositionOfTower f g Λ D := by
  apply iso_conjugate_eq_of_square
    (s := compositionPairIso
      (moduleCompactificationTorsionComparison f Λ C.first D.first).symm
      (moduleCompactificationTorsionComparison g Λ
        C.targetCompactification D.targetCompactification).symm)
    (t := (moduleCompactificationTorsionComparison (f ≫ g) Λ
      C.composite D.composite).symm)
  · rw [compositionPairIso_trans]
    congr 1
    · rw [← moduleExceptionalDirectImagePlusTorsionOfNonemptyIso_trans f Λ C.first D.first]
      simp
    · rw [← moduleExceptionalDirectImagePlusTorsionOfNonemptyIso_trans g Λ
        C.targetCompactification D.targetCompactification]
      simp
  · rw [← moduleExceptionalDirectImagePlusTorsionOfNonemptyIso_trans (f ≫ g) Λ
      C.composite D.composite]
    simp
  · exact moduleCompactifiedCompositionIso_refinement f g Λ a

/-- Any two supplied towers give the same map, by their actual common refinement. -/
theorem moduleExceptionalSuppliedCompositionOfTower_eq
    (C D : Hom.CompactifiedComposition f g) :
    moduleExceptionalSuppliedCompositionOfTower f g Λ C =
      moduleExceptionalSuppliedCompositionOfTower f g Λ D :=
  (moduleExceptionalSuppliedCompositionOfTower_refinement f g Λ
    (Hom.CompactifiedComposition.commonToLeft C D)).symm.trans
  (moduleExceptionalSuppliedCompositionOfTower_refinement f g Λ
    (Hom.CompactifiedComposition.commonToRight C D))

variable [Nonempty (Hom.CompactifiedComposition f g)]

/-- The canonical binary compositor of the chosen native torsion-valued functors. -/
def moduleExceptionalSuppliedCompositionIso :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ⋙
      moduleExceptionalDirectImagePlusTorsionOfNonempty g Λ ≅
    moduleExceptionalDirectImagePlusTorsionOfNonempty (f ≫ g) Λ :=
  moduleExceptionalSuppliedCompositionOfTower f g Λ (Classical.choice inferInstance)

/-- The canonical compositor equals the original map from every supplied tower. -/
theorem moduleExceptionalSuppliedCompositionIso_eq_ofTower
    (C : Hom.CompactifiedComposition f g) :
    moduleExceptionalSuppliedCompositionIso f g Λ =
      moduleExceptionalSuppliedCompositionOfTower f g Λ C :=
  moduleExceptionalSuppliedCompositionOfTower_eq f g Λ _ C

/-- The chosen compositor commutes with the canonical comparisons to every actual
supplied tower; the top arrow remains the original compactified composition. -/
theorem moduleExceptionalSuppliedCompositionIso_comparison
    (C : Hom.CompactifiedComposition f g) :
    compositionPairIso
        (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso f Λ C.first)
        (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso g Λ C.targetCompactification) ≪≫
      moduleCompactifiedCompositionIso f g Λ C =
    moduleExceptionalSuppliedCompositionIso f g Λ ≪≫
      moduleExceptionalDirectImagePlusTorsionOfNonemptyIso (f ≫ g) Λ C.composite := by
  rw [moduleExceptionalSuppliedCompositionIso_eq_ofTower f g Λ C]
  simp [moduleExceptionalSuppliedCompositionOfTower]

variable [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- On the original qcqs domain the supplied construction is the exact original
chosen compositor, not merely an isomorphism with the same endpoints. -/
theorem moduleExceptionalSuppliedCompositionIso_eq :
    moduleExceptionalSuppliedCompositionIso f g Λ = moduleExceptionalCompositionIso f g Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
