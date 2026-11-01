/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImage
public import Aglib.CategoryTheory.Functor.CompositionChoice

/-!
# Choice-independent composition of exceptional direct images

The original compactified composition maps are transported to the chosen native
unbounded functors over the stated torsion coefficient ring. Their actual refinement cube and an
      actual common
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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original tower composition, transported by the canonical comparisons. -/
def moduleExceptionalDirectImageUnboundedCompositionOfTower (C : Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImageUnbounded f Λ ⋙
      moduleExceptionalDirectImageUnbounded g Λ ≅
    moduleExceptionalDirectImageUnbounded (f ≫ g) Λ :=
  compositionPairIso
    (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C.first)
    (moduleExceptionalDirectImageUnboundedIso g Λ N hN hΛ C.targetCompactification) ≪≫
  moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ ≪≫
  (moduleExceptionalDirectImageUnboundedIso (f ≫ g) Λ N hN hΛ C.composite).symm

/-- A genuine tower refinement does not change the transported original map. -/
theorem moduleExceptionalDirectImageUnboundedCompositionOfTower_refinement
    {C D : Hom.CompactifiedComposition f g}
    (a : Hom.CompactifiedComposition.Refinement C D) :
    moduleExceptionalDirectImageUnboundedCompositionOfTower f g Λ N hN hΛ C =
      moduleExceptionalDirectImageUnboundedCompositionOfTower f g Λ N hN hΛ D := by
  apply iso_conjugate_eq_of_square
    (s := compositionPairIso
      (moduleUnboundedCompactificationComparison f Λ N hN hΛ C.first D.first).symm
      (moduleUnboundedCompactificationComparison g Λ N hN hΛ
        C.targetCompactification D.targetCompactification).symm)
    (t := (moduleUnboundedCompactificationComparison (f ≫ g) Λ N hN hΛ
      C.composite D.composite).symm)
  · rw [compositionPairIso_trans]
    congr 1
    · rw [← moduleExceptionalDirectImageUnboundedIso_trans f Λ N hN hΛ C.first D.first]
      simp
    · rw [← moduleExceptionalDirectImageUnboundedIso_trans g Λ N hN hΛ
        C.targetCompactification D.targetCompactification]
      simp
  · rw [← moduleExceptionalDirectImageUnboundedIso_trans (f ≫ g) Λ N hN hΛ
      C.composite D.composite]
    simp
  · exact moduleUnboundedCompactifiedCompositionIso_refinement f g Λ a N hN hΛ

/-- Any two supplied towers give the same map, by their actual common refinement. -/
theorem moduleExceptionalDirectImageUnboundedCompositionOfTower_eq
    (C D : Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImageUnboundedCompositionOfTower f g Λ N hN hΛ C =
      moduleExceptionalDirectImageUnboundedCompositionOfTower f g Λ N hN hΛ D :=
  (moduleExceptionalDirectImageUnboundedCompositionOfTower_refinement f g Λ N hN hΛ
    (Hom.CompactifiedComposition.commonToLeft C D)).symm.trans
  (moduleExceptionalDirectImageUnboundedCompositionOfTower_refinement f g Λ N hN hΛ
    (Hom.CompactifiedComposition.commonToRight C D))

/-- The canonical binary compositor of the chosen native unbounded functors. -/
def moduleExceptionalDirectImageUnboundedCompIso :
    moduleExceptionalDirectImageUnbounded f Λ ⋙
      moduleExceptionalDirectImageUnbounded g Λ ≅
    moduleExceptionalDirectImageUnbounded (f ≫ g) Λ :=
  moduleExceptionalDirectImageUnboundedCompositionOfTower f g Λ N hN hΛ (Classical.choice
      inferInstance)

/-- The canonical compositor equals the original map from every supplied tower. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_eq_ofTower
    (C : Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ =
      moduleExceptionalDirectImageUnboundedCompositionOfTower f g Λ N hN hΛ C :=
  moduleExceptionalDirectImageUnboundedCompositionOfTower_eq f g Λ N hN hΛ _ C

/-- The chosen compositor commutes with the canonical comparisons to every actual
supplied tower; the top arrow remains the original compactified composition. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_comparison
    (C : Hom.CompactifiedComposition f g) :
    compositionPairIso
        (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C.first)
        (moduleExceptionalDirectImageUnboundedIso g Λ N hN hΛ C.targetCompactification) ≪≫
      moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ =
    moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedIso (f ≫ g) Λ N hN hΛ C.composite := by
  rw [moduleExceptionalDirectImageUnboundedCompIso_eq_ofTower f g Λ N hN hΛ C]
  simp [moduleExceptionalDirectImageUnboundedCompositionOfTower]

end AlgebraicGeometry.Scheme.EtaleCohomology
