/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction

/-! # The original chart restriction and inverse-image unit -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]

/-- The chosen étale restriction comparison is normalized by the original unit. -/
@[reassoc]
theorem inverseImageEtaleIso_unit (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageAdjunction f).unit.app F ≫
        (directImage f).map ((inverseImageEtaleIso f).hom.app F) =
      ((siteEtalePostcomposeAdj f).sheafPushforwardContinuous
        (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology S)
        (Scheme.smallEtaleTopology X)).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app (inverseImageAdjunction f)
    ((siteEtalePostcomposeAdj f).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X)) F

/-- On each original test scheme the normalized unit is the actual site counit map. -/
@[reassoc]
theorem inverseImageEtaleIso_unit_app (F : AbelianSheaf.{u, u + 1} X)
    (U : X.Etale) :
    ((inverseImageAdjunction f).unit.app F).hom.app (op U) ≫
        ((inverseImageEtaleIso f).hom.app F).hom.app
          (op ((siteBaseChange f).obj U)) =
      F.obj.map ((siteEtalePostcomposeAdj f).counit.app U).op := by
  exact congrArg (fun h => h.hom.app (op U)) (inverseImageEtaleIso_unit f F)

end AlgebraicGeometry.Scheme.EtaleCohomology
