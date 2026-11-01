/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementCube
public import Aglib.CategoryTheory.Functor.CompositionChoice
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SuppliedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Composition

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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original tower composition, transported by the canonical comparisons. -/
def moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower (C :
      Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImageUnboundedOfNonempty f Λ ⋙
      moduleExceptionalDirectImageUnboundedOfNonempty g Λ ≅
    moduleExceptionalDirectImageUnboundedOfNonempty (f ≫ g) Λ :=
  compositionPairIso
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C.first)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso g Λ N hN hΛ C.targetCompactification) ≪≫
  moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ ≪≫
  (moduleExceptionalDirectImageUnboundedOfNonemptyIso (f ≫ g) Λ N hN hΛ C.composite).symm

/-- A genuine tower refinement does not change the transported original map. -/
theorem moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower_refinement
    {C D : Hom.CompactifiedComposition f g}
    (a : Hom.CompactifiedComposition.Refinement C D) :
    moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower f g Λ N hN hΛ C =
      moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower f g Λ N hN hΛ D := by
  apply iso_conjugate_eq_of_square
    (s := compositionPairIso
      (moduleUnboundedCompactificationComparison f Λ N hN hΛ C.first D.first).symm
      (moduleUnboundedCompactificationComparison g Λ N hN hΛ
        C.targetCompactification D.targetCompactification).symm)
    (t := (moduleUnboundedCompactificationComparison (f ≫ g) Λ N hN hΛ
      C.composite D.composite).symm)
  · rw [compositionPairIso_trans]
    congr 1
    · rw [← moduleExceptionalDirectImageUnboundedOfNonemptyIso_trans f Λ N hN hΛ C.first D.first]
      simp
    · rw [← moduleExceptionalDirectImageUnboundedOfNonemptyIso_trans g Λ N hN hΛ
        C.targetCompactification D.targetCompactification]
      simp
  · rw [← moduleExceptionalDirectImageUnboundedOfNonemptyIso_trans (f ≫ g) Λ N hN hΛ
      C.composite D.composite]
    simp
  · exact moduleUnboundedCompactifiedCompositionIso_refinement f g Λ a N hN hΛ

/-- Any two supplied towers give the same map, by their actual common refinement. -/
theorem moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower_eq
    (C D : Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower f g Λ N hN hΛ C =
      moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower f g Λ N hN hΛ D :=
  (moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower_refinement f g Λ N hN hΛ
    (Hom.CompactifiedComposition.commonToLeft C D)).symm.trans
  (moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower_refinement f g Λ N hN hΛ
    (Hom.CompactifiedComposition.commonToRight C D))

variable [Nonempty (Hom.CompactifiedComposition f g)]

/-- The canonical binary compositor of the chosen native unbounded functors. -/
def moduleExceptionalDirectImageUnboundedSuppliedCompIso :
    moduleExceptionalDirectImageUnboundedOfNonempty f Λ ⋙
      moduleExceptionalDirectImageUnboundedOfNonempty g Λ ≅
    moduleExceptionalDirectImageUnboundedOfNonempty (f ≫ g) Λ :=
  moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower f g Λ N hN hΛ
      (Classical.choice inferInstance)

/-- The canonical compositor equals the original map from every supplied tower. -/
theorem moduleExceptionalDirectImageUnboundedSuppliedCompIso_eq_ofTower
    (C : Hom.CompactifiedComposition f g) :
    moduleExceptionalDirectImageUnboundedSuppliedCompIso f g Λ N hN hΛ =
      moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower f g Λ N hN hΛ C :=
  moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower_eq f g Λ N hN hΛ _ C

/-- The chosen compositor commutes with the canonical comparisons to every actual
supplied tower; the top arrow remains the original compactified composition. -/
theorem moduleExceptionalDirectImageUnboundedSuppliedCompIso_comparison
    (C : Hom.CompactifiedComposition f g) :
    compositionPairIso
        (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C.first)
        (moduleExceptionalDirectImageUnboundedOfNonemptyIso g Λ N hN hΛ C.targetCompactification) ≪≫
      moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ =
    moduleExceptionalDirectImageUnboundedSuppliedCompIso f g Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedOfNonemptyIso (f ≫ g) Λ N hN hΛ C.composite := by
  rw [moduleExceptionalDirectImageUnboundedSuppliedCompIso_eq_ofTower f g Λ N hN hΛ C]
  simp [moduleExceptionalDirectImageUnboundedSuppliedCompositionOfTower]

variable [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- On the original qcqs domain the supplied construction is the exact original
chosen compositor, not merely an isomorphism with the same endpoints. -/
theorem moduleExceptionalDirectImageUnboundedSuppliedCompIso_eq :
    moduleExceptionalDirectImageUnboundedSuppliedCompIso f g Λ N hN hΛ =
      moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
