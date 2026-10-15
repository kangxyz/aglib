/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-!
# Open base change for the original geometric pullback mate

The canonical restriction/pullback isomorphism identifies the existing open
base-change isomorphism with the original `cartesianBaseChangeMap`. In particular
that original map is invertible for arbitrary module coefficients when the base
leg is an open immersion. No quasicoherence or flatness premise is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The inverse restriction/pullback comparison preserves the original adjunction unit. -/
theorem restrictFunctorIsoPullback_inv_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).inv.app M) =
      (restrictAdjunction f).unit.app M := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
    (pullbackPushforwardAdjunction f) M]
  simp only [restrictFunctorIsoPullback, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact CategoryTheory.Category.comp_id _

variable {W X T S : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S)
  (g : T ⟶ S) [IsOpenImmersion a] [IsOpenImmersion g] (h : IsPullback a b f g)

/-- The actual open base-change isomorphism is the original geometric pullback mate. -/
theorem cartesianOpenBaseChange_pullback (M : X.Modules) :
    (restrictFunctorIsoPullback g).inv.app ((pushforward f).obj M) ≫
      (cartesianOpenBaseChange a b f g h).hom.app M ≫
        (pushforward b).map ((restrictFunctorIsoPullback a).hom.app M) =
      (cartesianBaseChangeMap a b f g h).app M := by
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  change (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) ≫
      (pushforward g).map _ =
    (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) ≫
      (pushforward g).map ((cartesianBaseChangeMap a b f g h).app M)
  have hn := (cartesianPushforwardSquare a b f g h).hom.naturality
    ((restrictFunctorIsoPullback a).hom.app M)
  dsimp only [Functor.comp_map] at hn
  calc
    _ = (restrictAdjunction g).unit.app ((pushforward f).obj M) ≫
        (pushforward g).map ((cartesianOpenBaseChange a b f g h).hom.app M) ≫
        (pushforward g).map ((pushforward b).map
          ((restrictFunctorIsoPullback a).hom.app M)) := by
      simp only [Functor.map_comp]
      rw [← Category.assoc, restrictFunctorIsoPullback_inv_unit]
    _ = (pushforward f).map ((restrictAdjunction a).unit.app M) ≫
        (cartesianPushforwardSquare a b f g h).hom.app ((restrictFunctor a).obj M) ≫
        (pushforward g).map ((pushforward b).map
          ((restrictFunctorIsoPullback a).hom.app M)) := by
      rw [← Category.assoc, ← cartesianOpenBaseChange_unit a b f g h M]
      simp only [Category.assoc]
    _ = (pushforward f).map ((restrictAdjunction a).unit.app M) ≫
        (pushforward f).map ((pushforward a).map
          ((restrictFunctorIsoPullback a).hom.app M)) ≫
        (cartesianPushforwardSquare a b f g h).hom.app ((pullback a).obj M) := by
      rw [← hn]
    _ = (pushforward f).map ((pullbackPushforwardAdjunction a).unit.app M) ≫
        (cartesianPushforwardSquare a b f g h).hom.app ((pullback a).obj M) := by
      rw [← Category.assoc, ← Functor.map_comp]
      rw [show (restrictAdjunction a).unit.app M ≫
          (pushforward a).map ((restrictFunctorIsoPullback a).hom.app M) =
          (pullbackPushforwardAdjunction a).unit.app M from
        Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction a)
          (pullbackPushforwardAdjunction a) M]
    _ = _ := cartesianBaseChangeMap_unit a b f g h M

/-- Open base change makes the existing geometric mate invertible for every module sheaf. -/
theorem isIso_cartesianBaseChangeMap_of_isOpenImmersion (M : X.Modules) :
    IsIso ((cartesianBaseChangeMap a b f g h).app M) := by
  rw [← cartesianOpenBaseChange_pullback a b f g h M]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
