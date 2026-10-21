/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.PullbackComposition

/-!
# The actual pullback unit on a commutative triangle

The original coefficient units commute with the native pullback and pushforward
composition comparisons and equality transports.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y Z : Scheme.{u}}

/-- Original pullback units commute with the canonical triangle comparisons. -/
theorem pullbackUnit_triangle (F : X.Modules) (p : Y ⟶ X) (v : Z ⟶ Y)
    (q : Z ⟶ X) (h : v ≫ p = q) :
    (pullbackPushforwardAdjunction p).unit.app F ≫
      (pushforward p).map
        ((pullbackPushforwardAdjunction v).unit.app ((pullback p).obj F) ≫
          (pushforward v).map
            ((pullbackComp v p).hom.app F ≫ (pullbackCongr h).hom.app F)) ≫
      (pushforwardComp v p).hom.app ((pullback q).obj F) ≫
      (pushforwardCongr h).hom.app ((pullback q).obj F) =
        (pullbackPushforwardAdjunction q).unit.app F := by
  subst q
  have hp : (pushforwardCongr (rfl : v ≫ p = v ≫ p)).hom.app
      ((pullback (v ≫ p)).obj F) = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    rw [pushforwardCongr_hom_app_app]
    change ((pullback (v ≫ p)).obj F).presheaf.map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  have hl : (pullbackCongr (rfl : v ≫ p = v ≫ p)).hom.app F = 𝟙 _ := rfl
  rw [hl, Category.comp_id, hp, Category.comp_id]
  let e := (pullbackComp v p).app F
  have hu := Scheme.Cohomology.pullbackPushforwardAdjunction_unit_comp p v F
  have hv := congrArg (fun k => k ≫ (pushforward (v ≫ p)).map e.hom) hu
  have he : (pullbackComp v p).inv.app F ≫ e.hom = 𝟙 _ :=
    (pullbackComp v p).inv_hom_id_app F
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, he,
    CategoryTheory.Functor.map_id] at hv
  have hn := (pushforwardComp v p).hom.naturality e.hom
  dsimp only [CategoryTheory.Functor.comp_map, e, Iso.app_hom] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hn]
  exact hv

/-- The original coefficient arrow along a commutative pullback triangle. -/
def pullbackTriangleCoefficientMap (F : X.Modules) (p : Y ⟶ X) (v : Z ⟶ Y)
    (q : Z ⟶ X) (h : v ≫ p = q) :
    (pullback p).obj F ⟶ (pushforward v).obj ((pullback q).obj F) :=
  (pullbackPushforwardAdjunction v).unit.app ((pullback p).obj F) ≫
    (pushforward v).map
      ((pullbackComp v p).hom.app F ≫ (pullbackCongr h).hom.app F)

/-- The pushed coefficient map obtained from the original unit along a triangle. -/
def pullbackTrianglePushforwardMap (F : X.Modules) (p : Y ⟶ X) (v : Z ⟶ Y)
    (q : Z ⟶ X) (h : v ≫ p = q) :
    (pushforward p).obj ((pullback p).obj F) ⟶
      (pushforward q).obj ((pullback q).obj F) :=
  (pushforward p).map (pullbackTriangleCoefficientMap F p v q h) ≫
    (pushforwardComp v p).hom.app ((pullback q).obj F) ≫
    (pushforwardCongr h).hom.app ((pullback q).obj F)

/-- The triangle coefficient map preserves the original geometric unit. -/
theorem unit_pullbackTrianglePushforwardMap (F : X.Modules) (p : Y ⟶ X) (v : Z ⟶ Y)
    (q : Z ⟶ X) (h : v ≫ p = q) :
    (pullbackPushforwardAdjunction p).unit.app F ≫
      pullbackTrianglePushforwardMap F p v q h =
        (pullbackPushforwardAdjunction q).unit.app F :=
  pullbackUnit_triangle F p v q h

end AlgebraicGeometry.Scheme.Modules
