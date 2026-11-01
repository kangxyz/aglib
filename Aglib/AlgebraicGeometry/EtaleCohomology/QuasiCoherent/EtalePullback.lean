/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit

/-! # The original coefficient pullback on an étale chart

Only for an étale chart, literal restriction identifies the additive
coefficient with that of the native module pullback. The unit equation
identifies this isomorphism with the original inverse-image coefficient map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  (M : Y.Modules) [M.IsQuasicoherent]

/-- Literal restriction along an étale chart is the coefficient of the original
module pullback, through its native composition isomorphism. -/
def additiveCoefficientEtaleRestrictionIso :
    (etaleRestriction f).obj (additiveCoefficient Y M) ≅
      additiveCoefficient X ((pullback f).obj M) :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft (Scheme.Etale.forget X).op
      (additiveBaseRestrictionIso f M))

/-- The literal restriction unit is the same original pullback-section arrow. -/
theorem additiveCoefficientEtaleRestrictionIso_unit :
    (((siteEtalePostcomposeAdj f).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (smallEtaleTopology X)
      (smallEtaleTopology Y)).unit.app (additiveCoefficient Y M)) ≫
        (directImage f).map (additiveCoefficientEtaleRestrictionIso f M).hom =
      additiveCoefficientPullbackUnit f M := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (additiveSectionsPresheaf Y M).map
      ((Scheme.Etale.forget Y).map ((siteEtalePostcomposeAdj f).counit.app U.unop)).op ≫
        (additiveBaseRestrictionIso f M).hom.app
          (op ((Scheme.Etale.forget X).obj ((siteBaseChange f).obj U.unop))) =
    (additiveSectionsPresheaf Y M).map
      ((Over.mapPullbackAdj f).counit.app ((Scheme.Etale.forget Y).obj U.unop)).op ≫
        (additiveBaseRestrictionIso f M).hom.app
          (op ((Scheme.Etale.forget X).obj ((siteBaseChange f).obj U.unop)))
  congr 2

/-- The original inverse-image coefficient map is exactly the chart restriction
isomorphism, preceded by the original inverse-image/restriction comparison. -/
theorem additiveCoefficientPullback_eq_etaleRestriction :
    additiveCoefficientPullback f M =
      (inverseImageEtaleIso f).hom.app (additiveCoefficient Y M) ≫
        (additiveCoefficientEtaleRestrictionIso f M).hom := by
  apply ((inverseImageAdjunction f).homEquiv _ _).injective
  rw [additiveCoefficientPullback, Equiv.apply_symm_apply]
  change additiveCoefficientPullbackUnit f M =
    (inverseImageAdjunction f).unit.app (additiveCoefficient Y M) ≫
      (directImage f).map ((inverseImageEtaleIso f).hom.app (additiveCoefficient Y M) ≫
        (additiveCoefficientEtaleRestrictionIso f M).hom)
  rw [Functor.map_comp, ← Category.assoc,
    inverseImageEtaleIso_unit, additiveCoefficientEtaleRestrictionIso_unit]

/-- Invertibility is proved for actual étale charts, not asserted for arbitrary
flat base change. -/
instance additiveCoefficientPullback_isIso : IsIso (additiveCoefficientPullback f M) := by
  rw [additiveCoefficientPullback_eq_etaleRestriction]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
