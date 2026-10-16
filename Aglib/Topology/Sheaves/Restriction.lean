/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.ExtensionByZero

/-!
# The original restriction and direct-image adjunction

For an open subspace, the actual sectionwise restriction is left adjoint to
the original geometric direct image. The unique inverse-image comparison
retains this adjunction's original restriction unit. This supplies the unit
normalization needed to compare open cohomology with geometric pullback.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- Sectionwise restriction is left adjoint to the actual geometric direct image. -/
def openRestrictPushforwardAdjunction :
    U.sheafRestrict (C := AddCommGrpCat.{u}) ⊣ pushforward AddCommGrpCat.{u} U.inclusion' := by
  letI : U.isOpenEmbedding.functor.IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := U.isOpenEmbedding.functor_isContinuous
  letI : (Opens.map U.inclusion').IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology U) := by
    apply Functor.isContinuous_of_coverPreserving
    · exact compatiblePreserving_opens_map U.inclusion'
    · exact coverPreserving_opens_map U.inclusion'
  exact U.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

/-- The native restriction unit is the original presheaf restriction. -/
theorem openRestrictPushforwardAdjunction_unit_app
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (W : Opens X) :
    ((openRestrictPushforwardAdjunction U).unit.app F).hom.app (op W) =
      F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op := rfl

/-- Actual inverse image is canonically identified with sectionwise restriction using
the original restriction/direct-image adjunction. -/
def openRestrictionPullbackIso :
    pullback AddCommGrpCat.{u} U.inclusion' ≅ U.sheafRestrict (C := AddCommGrpCat.{u}) :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} U.inclusion').leftAdjointUniq
    (openRestrictPushforwardAdjunction U)

/-- The inverse-image comparison keeps the original adjunction unit. -/
theorem openRestrictionPullbackIso_unit
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} U.inclusion').unit.app F ≫
        (pushforward AddCommGrpCat.{u} U.inclusion').map
          ((openRestrictionPullbackIso U).hom.app F) =
      (openRestrictPushforwardAdjunction U).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The original inverse-image adjunction sends the comparison to actual restriction. -/
theorem openRestrictionPullbackIso_homEquiv
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} U.inclusion').homEquiv _ _
        ((openRestrictionPullbackIso U).hom.app F) =
      (openRestrictPushforwardAdjunction U).unit.app F :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ F

end TopCat.Sheaf
