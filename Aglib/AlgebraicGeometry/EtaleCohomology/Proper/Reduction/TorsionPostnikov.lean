/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleComparison
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Comparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SingleHigher
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ExchangeShift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic

/-! # Original derived exchange on bounded-below torsion cohomology

Original sheaf-level exchange on locally torsion coefficients supplies the
comparison on all homology singles. Native lower-bound preservation and
finite Postnikov windows give the same defined comparison on every D+
object with torsion cohomology, without an upper or dimension bound.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- Original all-degree exchange on locally torsion sheaves implies the
defined derived exchange on every D+ object with locally torsion homology.
The four supplied derived models remain independent. -/
theorem derivedBaseChangeMap_isIso_of_torsion_homology
    (hbc : ∀ (F : AbelianSheaf.{u, u + 1} X), IsTorsion X F →
      ∀ q : ℕ, IsIso ((higherBaseChangeMap f f' g g' h q).app F))
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X))
    (hK : ∀ i : ℤ, IsTorsion X
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) i).obj K)) :
    IsIso ((derivedBaseChangeMap f f' g g' h).app K) := by
  let τ := derivedBaseChangeMap f f' g g' h
  let : NatTrans.CommShift τ ℤ := derivedBaseChangeMap_commShift f f' g g' h
  refine DerivedCategory.Plus.isIso_app_of_homology_singles τ ?_ ?_ K ?_
  · intro L a hL
    let : L.IsGE a := hL
    let : ((derivedDirectImage f).obj L).IsGE a :=
      (directImage f).rightDerivedFunctorPlus_isGE L a
    exact (inverseImage g).rightDerivedFunctorPlus_isGE ((derivedDirectImage f).obj L) a
  · intro L a hL
    let : L.IsGE a := hL
    let : ((derivedInverseImage g').obj L).IsGE a :=
      (inverseImage g').rightDerivedFunctorPlus_isGE L a
    exact (directImage f').rightDerivedFunctorPlus_isGE ((derivedInverseImage g').obj L) a
  · intro i
    let M := (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) i).obj K
    have hM : IsIso (τ.app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj M)) :=
      (derivedBaseChangeMap_single_isIso_iff_higher f f' g g' h M).mpr (hbc M (hK i))
    let : IsIso (τ.app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj M)) := hM
    exact DerivedCategory.Plus.isIso_app_single_of_zero τ M i

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
