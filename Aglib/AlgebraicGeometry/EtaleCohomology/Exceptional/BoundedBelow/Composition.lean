/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementCube
public import Aglib.CategoryTheory.Functor.CompositionChoice

/-!
# Choice-independent composition of exceptional direct images

The original compactified composition maps are transported to the chosen native
bounded-below torsion functors. Their actual refinement cube and an actual common
refinement prove independence of the supplied compactification tower. This file
addresses binary composition; associativity and unit coherence are separate.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
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

/-- The original tower composition, transported by the canonical comparisons. -/
def moduleExceptionalCompositionOfTower (C : Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImagePlusTorsion f Λ ⋙
      moduleExceptionalDirectImagePlusTorsion g Λ ≅
    moduleExceptionalDirectImagePlusTorsion (f ≫ g) Λ :=
  compositionPairIso
    (moduleExceptionalDirectImagePlusTorsionIso f Λ C.first)
    (moduleExceptionalDirectImagePlusTorsionIso g Λ C.targetCompactification) ≪≫
  moduleCompactifiedCompositionIso f g Λ C ≪≫
  (moduleExceptionalDirectImagePlusTorsionIso (f ≫ g) Λ C.composite).symm

/-- A genuine tower refinement does not change the transported original map. -/
theorem moduleExceptionalCompositionOfTower_refinement
    {C D : Hom.CompactifiedComposition f g}
    (a : Hom.CompactifiedComposition.Refinement C D) :
    moduleExceptionalCompositionOfTower f g Λ C =
      moduleExceptionalCompositionOfTower f g Λ D := by
  apply iso_conjugate_eq_of_square
    (s := compositionPairIso
      (moduleCompactificationTorsionComparison f Λ C.first D.first).symm
      (moduleCompactificationTorsionComparison g Λ
        C.targetCompactification D.targetCompactification).symm)
    (t := (moduleCompactificationTorsionComparison (f ≫ g) Λ
      C.composite D.composite).symm)
  · rw [compositionPairIso_trans]
    congr 1
    · rw [← moduleExceptionalDirectImagePlusTorsionIso_trans f Λ C.first D.first]
      simp
    · rw [← moduleExceptionalDirectImagePlusTorsionIso_trans g Λ
        C.targetCompactification D.targetCompactification]
      simp
  · rw [← moduleExceptionalDirectImagePlusTorsionIso_trans (f ≫ g) Λ
      C.composite D.composite]
    simp
  · exact moduleCompactifiedCompositionIso_refinement f g Λ a

/-- Any two supplied towers give the same map, by their actual common refinement. -/
theorem moduleExceptionalCompositionOfTower_eq
    (C D : Hom.CompactifiedComposition f g) :
    moduleExceptionalCompositionOfTower f g Λ C =
      moduleExceptionalCompositionOfTower f g Λ D :=
  (moduleExceptionalCompositionOfTower_refinement f g Λ
    (Hom.CompactifiedComposition.commonToLeft C D)).symm.trans
  (moduleExceptionalCompositionOfTower_refinement f g Λ
    (Hom.CompactifiedComposition.commonToRight C D))

/-- The canonical binary compositor of the chosen native torsion-valued functors. -/
def moduleExceptionalCompositionIso :
    moduleExceptionalDirectImagePlusTorsion f Λ ⋙
      moduleExceptionalDirectImagePlusTorsion g Λ ≅
    moduleExceptionalDirectImagePlusTorsion (f ≫ g) Λ :=
  moduleExceptionalCompositionOfTower f g Λ (Classical.choice inferInstance)

/-- The canonical compositor equals the original map from every supplied tower. -/
theorem moduleExceptionalCompositionIso_eq_ofTower
    (C : Hom.CompactifiedComposition f g) :
    moduleExceptionalCompositionIso f g Λ = moduleExceptionalCompositionOfTower f g Λ C :=
  moduleExceptionalCompositionOfTower_eq f g Λ _ C

/-- The chosen compositor commutes with the canonical comparisons to every actual
supplied tower; the top arrow remains the original compactified composition. -/
theorem moduleExceptionalCompositionIso_comparison
    (C : Hom.CompactifiedComposition f g) :
    compositionPairIso
        (moduleExceptionalDirectImagePlusTorsionIso f Λ C.first)
        (moduleExceptionalDirectImagePlusTorsionIso g Λ C.targetCompactification) ≪≫
      moduleCompactifiedCompositionIso f g Λ C =
    moduleExceptionalCompositionIso f g Λ ≪≫
      moduleExceptionalDirectImagePlusTorsionIso (f ≫ g) Λ C.composite := by
  rw [moduleExceptionalCompositionIso_eq_ofTower f g Λ C]
  simp [moduleExceptionalCompositionOfTower]

end AlgebraicGeometry.Scheme.EtaleCohomology
