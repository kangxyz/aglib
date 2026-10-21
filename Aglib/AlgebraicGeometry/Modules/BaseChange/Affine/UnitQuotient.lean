/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine

/-!
# Affine pushforward and the original base-change units

For a closed change of base these pullback-pushforward objects are the actual
coefficient quotients. The comparison requires no flatness of either morphism.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y T : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (g : T ⟶ Y)
  (M : X.Modules) [M.IsQuasicoherent]

/-- The canonical affine base-change comparison after pushing to the original base. -/
def affinePushforwardUnitIso :
    (pushforward f).obj ((pushforward (Limits.pullback.fst f g)).obj
      ((pullback (Limits.pullback.fst f g)).obj M)) ≅
    (pushforward g).obj ((pullback g).obj ((pushforward f).obj M)) := by
  let : IsIso (moduleBaseChangeMap f g M) := moduleBaseChangeMap_isIso f g M
  exact (cartesianPushforwardSquare (Limits.pullback.fst f g) (Limits.pullback.snd f g)
    f g (IsPullback.of_hasPullback f g)).app
      ((pullback (Limits.pullback.fst f g)).obj M) ≪≫
        (pushforward g).mapIso (asIso (moduleBaseChangeMap f g M)).symm

/-- The canonical comparison intertwines the original geometric units. -/
@[reassoc (attr := simp)]
theorem affinePushforwardUnitIso_unit :
    (pushforward f).map
        ((pullbackPushforwardAdjunction (Limits.pullback.fst f g)).unit.app M) ≫
      (affinePushforwardUnitIso f g M).hom =
        (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) := by
  let : IsIso (moduleBaseChangeMap f g M) := moduleBaseChangeMap_isIso f g M
  dsimp only [affinePushforwardUnitIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc]
  change ((pushforward f).map
      ((pullbackPushforwardAdjunction (Limits.pullback.fst f g)).unit.app M) ≫
    (cartesianPushforwardSquare (Limits.pullback.fst f g) (Limits.pullback.snd f g)
      f g (IsPullback.of_hasPullback f g)).hom.app
        ((pullback (Limits.pullback.fst f g)).obj M)) ≫
      (pushforward g).map (inv (moduleBaseChangeMap f g M)) = _
  rw [moduleBaseChangeMap_unit, Category.assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Modules
