/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Pullback

/-! # The original value-lift and inverse-image mate

Continuous direct image commutes pointwise with the native additive value lift.
Its native mate constructs the inverse-image coefficient map and its whole unit
equation. No preservation of Kan extensions, injectives, or invertibility of the
mate is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h d k v t

variable {C : Type c} [Category.{h} C] {D : Type d} [Category.{k} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max v t} J K).IsRightAdjoint]

/-- The actual direct-image/value-lift square is pointwise the identity. -/
def valueLiftDirectImageIso :
    G.sheafPushforwardContinuous AddCommGrpCat.{v} J K ⋙ valueLift.{c, h, v, t} J ≅
      valueLift.{d, k, v, t} K ⋙
        G.sheafPushforwardContinuous AddCommGrpCat.{max v t} J K := Iso.refl _

/-- The original inverse-image coefficient map, as the native mate of the
pointwise direct-image square. It need not be an isomorphism. -/
def valueLiftPullbackMap :
    valueLift.{c, h, v, t} J ⋙ G.sheafPullback AddCommGrpCat.{max v t} J K ⟶
      G.sheafPullback AddCommGrpCat.{v} J K ⋙ valueLift.{d, k, v, t} K :=
  ((mateEquiv (G.sheafAdjunctionContinuous AddCommGrpCat.{v} J K)
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max v t} J K)).symm
      (TwoSquare.mk _ _ _ _ (valueLiftDirectImageIso.{c, h, d, k, v, t} G J K).hom)).natTrans

/-- The whole mate retains the two original inverse-image units and the
pointwise direct-image comparison. -/
@[reassoc]
theorem valueLiftPullbackMap_unit (F : Sheaf J AddCommGrpCat.{v}) :
    (valueLift.{c, h, v, t} J).map
        ((G.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app F) ≫
      (valueLiftDirectImageIso.{c, h, d, k, v, t} G J K).hom.app
        ((G.sheafPullback AddCommGrpCat.{v} J K).obj F) =
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max v t} J K).unit.app
        ((valueLift.{c, h, v, t} J).obj F) ≫
      (G.sheafPushforwardContinuous AddCommGrpCat.{max v t} J K).map
        ((valueLiftPullbackMap.{c, h, d, k, v, t} G J K).app F) :=
  unit_mateEquiv_symm (G.sheafAdjunctionContinuous AddCommGrpCat.{v} J K)
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max v t} J K)
    (TwoSquare.mk _ _ _ _ (valueLiftDirectImageIso.{c, h, d, k, v, t} G J K).hom) F

end CategoryTheory.Sheaf.BasisAcyclicity
