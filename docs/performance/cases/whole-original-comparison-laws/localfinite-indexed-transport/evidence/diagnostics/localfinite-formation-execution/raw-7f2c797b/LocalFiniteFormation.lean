/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.NoetherianComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineTests
public import Mathlib.GroupTheory.OrderOfElement
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection

/-! # Formation-only diagnostic for the original finite source comparison

The exact complete original proposition occurs only as an unused theorem binder.
This source proves True, not the original comparison or the production module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eX eS eX' eS'

attribute [local instance] hasSheafifyLarge

/-- Check only the original full proposition at the actual native heads. -/
theorem localFiniteSourceComparison_formation
    (_h : ∀
      {X S X' S' : Scheme.{u}}
      [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
      [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
      [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
      [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
      (f : X ⟶ S) [IsFinite f]
      (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
      (_hSquare : IsPullback g' f' f g) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
      (_hF : Function.Bijective (cohomologyPullback.{u, eS, eS'} g
      ((directImage f).obj F) q)),
      Function.Bijective (cohomologyPullback.{u, eX, eX'} g' F q)) : True :=
  True.intro

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
