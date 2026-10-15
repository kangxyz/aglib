/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The original geometric base-change mate

A specified cartesian square determines the ordinary pullback/direct-image mate from
its original pushforward comparison. Both unit and counit compatibility equations
are retained, without an open-immersion or flatness hypothesis.
-/

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/CartesianBaseChange.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 52]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j)
/-- The original pushforward square comparison. -/
def cartesianPushforwardSquare : pushforward a ⋙ pushforward f ≅ pushforward b ⋙ pushforward j :=
  pushforwardComp a f ≪≫ pushforwardCongr h.w ≪≫ (pushforwardComp b j).symm
/-- The original ordinary pullback/direct-image base-change mate of an actual cartesian square. -/
def cartesianBaseChangeMap :
    pushforward f ⋙ Scheme.Modules.pullback j ⟶ Scheme.Modules.pullback a ⋙ pushforward b :=
  ((mateEquiv (pullbackPushforwardAdjunction a) (pullbackPushforwardAdjunction j)).symm
    (TwoSquare.mk _ _ _ _ (cartesianPushforwardSquare a b f j h).hom)).natTrans
/-- The actual base-change mate retains both original geometric adjunction units. -/
theorem cartesianBaseChangeMap_unit (M : U.Modules) :
    (pushforward f).map ((pullbackPushforwardAdjunction a).unit.app M) ≫
      (cartesianPushforwardSquare a b f j h).hom.app ((Scheme.Modules.pullback a).obj M) =
    (pullbackPushforwardAdjunction j).unit.app ((pushforward f).obj M) ≫
      (pushforward j).map ((cartesianBaseChangeMap a b f j h).app M) :=
  unit_mateEquiv_symm (pullbackPushforwardAdjunction a) (pullbackPushforwardAdjunction j)
    (TwoSquare.mk _ _ _ _ (cartesianPushforwardSquare a b f j h).hom) M
/-- The same actual base-change mate retains the original geometric counits. -/
theorem cartesianBaseChangeMap_counit (M : W.Modules) :
    (Scheme.Modules.pullback j).map ((cartesianPushforwardSquare a b f j h).hom.app M) ≫
      (pullbackPushforwardAdjunction j).counit.app ((pushforward b).obj M) =
    (cartesianBaseChangeMap a b f j h).app ((pushforward a).obj M) ≫
      (pushforward b).map ((pullbackPushforwardAdjunction a).counit.app M) :=
  mateEquiv_counit_symm (pullbackPushforwardAdjunction a) (pullbackPushforwardAdjunction j)
    (TwoSquare.mk _ _ _ _ (cartesianPushforwardSquare a b f j h).hom) M
end AlgebraicGeometry.Scheme.Modules
