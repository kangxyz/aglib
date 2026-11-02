/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.Plus.HomologyIsIso

/-! # The original derived-single and all-degree exchange criteria

The published source/homology/target transport identifies the homology of
the original derived exchange with the original higher-image exchange.
Both actual sides on a source single are nonnegative. Thus invertibility of
all original natural-degree maps is equivalent to invertibility of the same
original derived-single component, without an extra H0 or boundedness premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original all-degree sheaf exchange is the complete homology test for
the same original derived exchange on a source single. All four declared
derived-category universes remain independent. -/
theorem derivedBaseChangeMap_single_isIso_iff_higher
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((derivedBaseChangeMap f f' g g' h).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) ↔
      ∀ q : ℕ, IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  constructor
  · intro hF q
    have := hF
    exact higherBaseChangeMap_isIso_app_of_derived f f' g g' h F q
  · intro hF
    let K := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F
    have h₁ : ((derivedDirectImage f).obj K).IsGE 0 :=
      (directImage f).rightDerivedFunctorPlus_isGE K 0
    have h₂ : ((derivedInverseImage g).obj ((derivedDirectImage f).obj K)).IsGE 0 :=
      (inverseImage g).rightDerivedFunctorPlus_isGE _ 0
    have h₃ : ((derivedInverseImage g').obj K).IsGE 0 :=
      (inverseImage g').rightDerivedFunctorPlus_isGE K 0
    have h₄ : ((derivedDirectImage f').obj ((derivedInverseImage g').obj K)).IsGE 0 :=
      (directImage f').rightDerivedFunctorPlus_isGE _ 0
    have : ((derivedDirectImage f ⋙ derivedInverseImage g).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)).IsGE 0 := h₂
    have : ((derivedInverseImage g' ⋙ derivedDirectImage f').obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)).IsGE 0 := h₄
    apply (DerivedCategory.Plus.isIso_iff_homology_nat _).mpr
    intro q
    exact (CategoryTheory.isIso_app_iff_of_whiskered_transport
      (higherBaseChangeSourceIso f g q) (derivedBaseChangeMap f f' g g' h)
      (higherBaseChangeTargetIso f' g' q) (higherBaseChangeMap f f' g g' h q)
      (higherBaseChangeMap_eq_transport f f' g g' h q) F).mp (hF q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
