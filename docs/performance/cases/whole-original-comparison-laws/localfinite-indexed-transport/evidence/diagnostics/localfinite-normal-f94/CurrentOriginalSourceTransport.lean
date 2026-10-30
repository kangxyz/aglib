/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.NoetherianComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineTests
public import Mathlib.GroupTheory.OrderOfElement
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparisonValues
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection

/-! # Current original inverse-source transport

The original ordinary source equation is proved using only the current original
composition law and the V28 generic transport helper. This is the complete source
equation, with no Ext-world, cohomology-coefficient or degree input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge

/-- The current generic transport helper proves the literal original ordinary
inverse-source transport and composition equation. -/
theorem diag_original_sourceSecond_v28
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (A : AddCommGrpCat.{u + 1}) :
    ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫
        (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h) ≪≫
          inverseImageComp f g').hom.app
            ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj A) =
      ((inverseImageConstantIso g').app A).inv ≫
        (inverseImage g').map ((inverseImageConstantIso f).app A).inv := by
  have hSourceComp := inverseImageComp_constant_inv f g' A
  exact Functor.sourceInverse_composite_transport
    (fun k : X' ⟶ S => inverseImage k) (fun k => inverseImageConstantIso k) h
    (inverseImageConstantIso f) (inverseImageConstantIso g') (inverseImageComp f g')
    A hSourceComp

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
