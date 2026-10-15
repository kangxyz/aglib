/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian

/-!
# Pasting the canonical cartesian base-change maps

Successive changes of base give the canonical map for the composite change of
base, through the original pullback-composition comparisons. The statement
applies to arbitrary module sheaves and cartesian squares; it has no flatness,
quasicoherence, or affineness hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme.Modules

/-- The forward pullback-composition comparison is conjugate to the inverse
of the original pushforward-composition comparison. -/
theorem conjugateEquiv_pullbackComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  apply (cancel_mono (pushforwardComp f g).hom).mp
  rw [Iso.inv_hom_id]
  rw [← conjugateEquiv_pullbackComp_inv f g, conjugateEquiv_comp]
  simp

/-- The actual cartesian base-change mate is coherent with two successive
changes of base, using the original composition isomorphisms on both sides. -/
theorem cartesianBaseChangeMap_comp
    {W X T S W' T' : Scheme.{u}}
    (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (h : IsPullback a b f g)
    (c : W' ⟶ W) (d : W' ⟶ T') (v : T' ⟶ T)
    (h' : IsPullback c d b v) (H : IsPullback (c ≫ a) d f (v ≫ g))
    (M : X.Modules) :
    (pullbackComp v g).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap (c ≫ a) d f (v ≫ g) H).app M =
      (pullback v).map ((cartesianBaseChangeMap a b f g h).app M) ≫
        (cartesianBaseChangeMap c d b v h').app ((pullback a).obj M) ≫
          (pushforward d).map ((pullbackComp c a).hom.app M) := by
  let α : TwoSquare (pushforward f) (pullback a) (pullback g) (pushforward b) :=
    TwoSquare.mk _ _ _ _ (cartesianBaseChangeMap a b f g h)
  let β : TwoSquare (pushforward b) (pullback c) (pullback v) (pushforward d) :=
    TwoSquare.mk _ _ _ _ (cartesianBaseChangeMap c d b v h')
  let γ : TwoSquare (pushforward f) (pullback (c ≫ a)) (pullback (v ≫ g))
      (pushforward d) :=
    TwoSquare.mk _ _ _ _ (cartesianBaseChangeMap (c ≫ a) d f (v ≫ g) H)
  have hsquare : γ.whiskerRight (pullbackComp v g).hom =
      (α ≫ᵥ β).whiskerLeft (pullbackComp c a).hom := by
    apply (mateEquiv (pullbackPushforwardAdjunction (c ≫ a))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction v))).injective
    rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp,
      conjugateEquiv_pullbackComp_hom, conjugateEquiv_pullbackComp_hom, mateEquiv_hcomp]
    simp only [α, β, γ, cartesianBaseChangeMap, Equiv.apply_symm_apply]
    apply TwoSquare.ext
    intro N
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Functor.comp_obj, pushforward_obj_obj, Hom.comp_base,
      TopologicalSpace.Opens.map_comp_obj, TwoSquare.whiskerBottom_app, Hom.comp_app,
      pushforwardComp_inv_app_app, Category.comp_id, TwoSquare.whiskerTop_app,
      TwoSquare.hComp_app, pushforward_map_app, Category.id_comp]
    change N.presheaf.map _ = N.presheaf.map _ ≫ N.presheaf.map _
    rw [← N.presheaf.map_comp]
    congr 1
  have he := congrArg (fun δ => δ.app M) hsquare
  simpa [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp, α, β, γ] using he

end AlgebraicGeometry.Scheme.Modules
