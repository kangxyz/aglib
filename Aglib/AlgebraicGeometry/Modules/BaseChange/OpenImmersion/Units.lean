/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-!
# Composing the original units in an open cartesian square

The actual pullback/restriction mate identifies the two composite coefficient
arrows through a cartesian open square. Both arrows use the original units,
native direct-image composition, and native equality comparison. This is
the coefficient equation needed by geometric cohomology restriction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {W Y U X : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ U) (f : Y ⟶ X) (j : U ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- The inverse of the original pullback/restriction mate makes the two original
composite module coefficient units equal. -/
theorem cartesianPullbackBaseChangeMate_inv_unit_comp (M : X.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫
        (pushforward f).map
          ((restrictAdjunction a).unit.app ((pullback f).obj M) ≫
            (pushforward a).map (inv ((cartesianPullbackBaseChangeMate a b f j h).app M))) ≫
        (pushforwardComp a f).hom.app ((pullback b).obj (M.restrict j)) ≫
        (pushforwardCongr h.w).hom.app ((pullback b).obj (M.restrict j)) =
      (restrictAdjunction j).unit.app M ≫
        (pushforward j).map ((pullbackPushforwardAdjunction b).unit.app (M.restrict j)) ≫
        (pushforwardComp b j).hom.app ((pullback b).obj (M.restrict j)) := by
  let N := (pullback f).obj M
  let P := (pullback b).obj (M.restrict j)
  let e : P ≅ N.restrict a := asIso ((cartesianPullbackBaseChangeMate a b f j h).app M)
  have hei : e.inv = inv ((cartesianPullbackBaseChangeMate a b f j h).app M) :=
    asIso_inv _
  have he : (restrictFunctor j).map ((pullbackPushforwardAdjunction f).unit.app M) ≫
      (cartesianOpenBaseChange a b f j h).hom.app N ≫ (pushforward b).map e.inv =
        (pullbackPushforwardAdjunction b).unit.app (M.restrict j) := by
    rw [← Category.assoc, cartesianOpenBaseChange_pullback_unit a b f j h M]
    change ((pullbackPushforwardAdjunction b).unit.app (M.restrict j) ≫
      (pushforward b).map e.hom) ≫ (pushforward b).map e.inv = _
    rw [Category.assoc, ← Functor.map_comp, e.hom_inv_id]
    erw [(pushforward b).map_id P]
    exact Category.comp_id _
  let s : (restrictFunctor j).obj M ⟶ (pushforward b).obj (N.restrict a) :=
    (restrictFunctor j).map ((pullbackPushforwardAdjunction f).unit.app M) ≫
      (cartesianOpenBaseChange a b f j h).hom.app N
  have hs : (restrictAdjunction j).homEquiv _ _ s =
      (pullbackPushforwardAdjunction f).unit.app M ≫
        (pushforward f).map ((restrictAdjunction a).unit.app N) ≫
        (cartesianPushforwardSquare a b f j h).hom.app (N.restrict a) :=
    cartesianOpenBaseChange_homEquiv a b f j h (E := M) (M := N)
      ((pullbackPushforwardAdjunction f).unit.app M)
  have he' : s ≫ (pushforward b).map e.inv =
      (pullbackPushforwardAdjunction b).unit.app (M.restrict j) := by
    simpa only [s, Category.assoc] using he
  have hr := (restrictAdjunction j).homEquiv_naturality_right s
    ((pushforward b).map e.inv)
  have hw : (pullbackPushforwardAdjunction f).unit.app M ≫
      (pushforward f).map ((restrictAdjunction a).unit.app N) ≫
      (cartesianPushforwardSquare a b f j h).hom.app (N.restrict a) ≫
      (pushforward j).map ((pushforward b).map e.inv) =
        (restrictAdjunction j).unit.app M ≫
          (pushforward j).map ((pullbackPushforwardAdjunction b).unit.app (M.restrict j)) := by
    calc
      _ = ((restrictAdjunction j).homEquiv _ _ s) ≫
          (pushforward j).map ((pushforward b).map e.inv) := by
        rw [hs]
        simp only [Category.assoc]
      _ = (restrictAdjunction j).homEquiv _ _ (s ≫ (pushforward b).map e.inv) := hr.symm
      _ = (restrictAdjunction j).homEquiv _ _
          ((pullbackPushforwardAdjunction b).unit.app (M.restrict j)) :=
        congrArg ((restrictAdjunction j).homEquiv _ _) he'
      _ = _ := rfl
  have hn := (cartesianPushforwardSquare a b f j h).hom.naturality e.inv
  dsimp only [Functor.comp_map] at hn
  erw [← hn] at hw
  have hs : (pullbackPushforwardAdjunction f).unit.app M ≫
      (pushforward f).map
        ((restrictAdjunction a).unit.app N ≫ (pushforward a).map e.inv) ≫
      (cartesianPushforwardSquare a b f j h).hom.app P =
        (restrictAdjunction j).unit.app M ≫
          (pushforward j).map ((pullbackPushforwardAdjunction b).unit.app (M.restrict j)) := by
    simpa only [Functor.comp_obj, Functor.map_comp, Category.assoc] using hw
  have ht := congrArg (fun t => t ≫ (pushforwardComp b j).hom.app P) hs
  simpa only [hei, cartesianPushforwardSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id] using ht

end AlgebraicGeometry.Scheme.Modules
